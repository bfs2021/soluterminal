package main

import (
	"context"
	"encoding/json"
	"flag"
	"io"
	"log"
	"net"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"runtime"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	gopty "github.com/aymanbagabas/go-pty"

	"soluterminal/grid"
)

// exitLingerDuration is how long the agent keeps its Unix socket
// accepting connections AFTER the child exits, so a daemon still
// mid-dial can connect, read FrameExit, and see a clean exit code
// instead of "dial: no such file or directory". Fixes the race where
// a short-lived command (e.g. `echo hi`) makes the whole spawn fail
// because teardown beats the daemon's retry loop.
const exitLingerDuration = 3 * time.Second

// socketRebindCheckInterval is how often a live agent verifies its own socket
// FILE still exists. If a daemon path unlinks it (resume/restore, native switch,
// background-resume, the startup orphan-socket sweep), the agent re-binds the
// path within one interval so a reconnecting daemon can still dial it instead of
// killing+respawning the session — see the "Socket self-heal" block in runAgent.
const socketRebindCheckInterval = time.Second

// childIO abstracts the agent's link to its child so the same fan-out +
// client-bridge code serves a PTY child (terminal panes) and a pipe child
// (--no-pty). A headless `claude -p --input-format stream-json` REFUSES a
// TTY/PTY stdin ("Input must be provided either through stdin or as a
// prompt argument when using --print") and needs real pipes. gopty.Pty
// satisfies this interface directly; pipeIO wraps an os.Pipe pair.
type childIO interface {
	io.Reader
	io.Writer
	Resize(cols, rows int) error
	Close() error
}

// pipeIO is the --no-pty child link: child stdout(+stderr) on r, child
// stdin on w. Resize is a no-op (no window size without a tty).
type pipeIO struct {
	r io.ReadCloser
	w io.WriteCloser
}

func (p *pipeIO) Read(b []byte) (int, error)  { return p.r.Read(b) }
func (p *pipeIO) Write(b []byte) (int, error) { return p.w.Write(b) }
func (p *pipeIO) Resize(int, int) error       { return nil }
func (p *pipeIO) Close() error {
	rErr := p.r.Close()
	wErr := p.w.Close()
	if rErr != nil {
		return rErr
	}
	return wErr
}

// runAgent implements the `solud agent ...` subcommand.
//
// One agent process holds one PTY for one pane. It's spawned by the daemon
// with Setsid=true so it survives daemon death. The daemon (and any other
// clients) connect to it via a Unix socket.
//
// Lifecycle:
//   - open the Unix socket at --socket
//   - spawn the child command in a PTY (via go-pty — abstracts over
//     openpty() on Unix and ConPTY on Windows; this file is still
//     Unix-only because the signal-forwarding + process-group kill
//     path below uses Unix-only syscalls)
//   - fan PTY bytes out to all connected clients
//   - read clients' frames and forward them to the PTY
//   - when the child exits, broadcast FrameExit and close
//   - clean up the socket file on exit
func runAgent() int {
	fs := flag.NewFlagSet("agent", flag.ExitOnError)
	socketPath := fs.String("socket", "", "Unix socket path (required)")
	ownerRetirementPane := fs.String("owner-retirement-pane", "", "exact managed owner pane eligible for conditional retirement")
	cwd := fs.String("cwd", "", "working directory")
	cols := fs.Uint("cols", 120, "initial cols")
	rows := fs.Uint("rows", 32, "initial rows")
	envStr := fs.String("env", "", "extra env vars, comma-separated KEY=VALUE")
	noPty := fs.Bool("no-pty", false, "wire the child to pipes instead of a PTY (headless stream-json agents like `claude -p` refuse a TTY stdin)")
	provider := fs.String("provider", "", "LLM backend for the child claude: \"\" (Anthropic) or \"glm\" (Z.ai)")
	dataDir := fs.String("data-dir", "", "daemon data dir for diagnostics and provider settings")
	_ = fs.Parse(os.Args[2:])
	args := fs.Args()
	if *socketPath == "" {
		log.Fatalf("--socket is required")
	}
	if len(args) == 0 {
		log.Fatalf("command required after --")
	}

	// If the socket file exists, it's stale (previous agent crashed).
	// net.Listen("unix", ...) would fail with "address already in use".
	_ = os.Remove(*socketPath)

	ln, err := net.Listen("unix", *socketPath)
	if err != nil {
		log.Fatalf("listen %s: %v", *socketPath, err)
	}
	// Tight permissions — only the current user.
	_ = os.Chmod(*socketPath, 0o600)

	// Socket self-heal. The daemon reaches us by CONNECTING to *socketPath.
	// Several daemon paths (resume/restore, native switch, background-resume,
	// the startup orphan-socket sweep) os.Remove() that file while we're still
	// alive — and once the socket FILE is unlinked we are unreachable BY PATH
	// even though our listener is still bound to the now-anonymous inode. A
	// daemon auto-update then can't dial us, logs "agent alive but socket file
	// gone", and kills+respawns us — interrupting the in-flight turn (the
	// "session was resumed; ask again" symptom). To stay reachable we guard the
	// listener behind a mutex and let a watchdog (below) re-bind the path if it
	// disappears. activeLn is always the listener currently bound to *socketPath.
	var lnMu sync.Mutex
	activeLn := ln
	shuttingDown := false
	closeActiveListener := func() {
		lnMu.Lock()
		shuttingDown = true
		_ = activeLn.Close()
		lnMu.Unlock()
	}
	defer func() {
		closeActiveListener()
		_ = os.Remove(*socketPath)
	}()

	// Build the child environment (shared by PTY and pipe modes). Strip any
	// inherited Claude Code session-context vars first: if the daemon was
	// launched from inside a Claude Code session (e.g. a `claude` run that
	// started the relay/daemon), its CLAUDE_CODE_SESSION_ID + CLAUDE_CODE_CHILD_
	// SESSION leak down into every pane we spawn — making the pane's own
	// `claude` attach as a NESTED "child session" that never writes its own
	// transcript (empty Activity tab / 0-turn cockpit). A pane is a fresh
	// top-level terminal, so these must never be inherited; a real `claude` run
	// sets its own. See stripInheritedClaudeEnv. (The PTY/pipe child creation
	// itself happens in the *noPty branch below, sharing this env.)
	env := stripInheritedClaudeEnv(os.Environ())
	if *envStr != "" {
		if paneBroker.agentInheritedEnv != nil {
			env = paneBroker.agentInheritedEnv(env, strings.Split(*envStr, ","))
		}
	}
	env = append(env, "TERM=xterm-256color", "COLORTERM=truecolor")
	// BSD ls on macOS reads $LSCOLORS directly. Setting a tuned value here
	// fixes the blue-on-green other-writable-dir issue for macOS users.
	// Linux/WSL users don't use $LSCOLORS (their GNU ls reads $LS_COLORS
	// via dircolors+~/.dircolors — covered in ensureDircolorsFile), so
	// setting it here is harmless on Linux. User's shell rc can override.
	env = append(env, "LSCOLORS="+safeLSCOLORS)
	if *envStr != "" {
		for _, kv := range strings.Split(*envStr, ",") {
			if kv != "" {
				env = append(env, kv)
			}
		}
	}
	if paneBrokerActive(env) {
		// Apply after the comma-delimited agent wire format is decoded: a
		// NO_PROXY list must not be split into unrelated environment entries.
		if paneBroker.agentEnv != nil {
			env = paneBroker.agentEnv(env)
		}
	}
	// Ensure ~/.local/bin (the native Claude installer's target) is on PATH for
	// EVERY pane child — shells included. Without this a fresh shell pane where
	// the user types `claude` right after installing it via the in-app banner
	// hits "command not found": the binary is in ~/.local/bin, but a shell pane
	// inherits only the daemon's slim PATH and ~/.local/bin lands on PATH only
	// for command panes that go through the bash -lc login wrap (loginShellInit).
	// This single choke point fixes it for all pane kinds. (Idempotent.)
	env = ensureLocalBinOnPath(env)
	// Bash pane children import this pane-scoped Codex function, including the
	// interactive shell reached after a managed agent exits. A Codex TUI typed
	// there must not reconnect to the machine-wide app-server approval stream.
	env = codexPaneShellEnv(args[0], env)

	// Windows: the daemon inherits a PATH SNAPSHOT from its launcher, and unlike
	// Unix there is no `bash -lc` login wrap to re-source the profile per pane. So
	// a tool added to the User/Machine PATH AFTER the long-lived daemon started —
	// most commonly a Claude Code install — is missing from every pane, and the
	// user sees `claude` "not recognized" in the pane even though a freshly-opened
	// PowerShell finds it. Rebuild PATH from the live registry (the same source a
	// fresh shell reads), UNIONed with the inherited PATH so nothing already
	// working is dropped. No-op off Windows. (See feedback #8/#9.)
	env = mergeRegistryPath(env)
	// Codex's standalone Windows installer writes the visible command to a fixed
	// user-level bin dir. If SoluTerminal was already running when Codex was
	// installed, some launcher environments can keep serving the old PATH even
	// after the installer updates the registry. Self-heal that exact install dir
	// when it exists so new PowerShell panes can run `codex` immediately. This
	// also covers WSL-daemon -> Windows-process panes (`pwsh.exe`) where the
	// daemon is a Linux binary but the child interprets PATH as a Windows PATH.
	env = ensureKnownWindowsCliDirsOnPath(env, args[0])

	// GLM provider: route this pane's claude to Z.ai. This block MUST stay
	// AFTER stripInheritedClaudeEnv above (it strips every CLAUDE_CODE_*, which
	// would silently delete the CLAUDE_CODE_AUTO_COMPACT_WINDOW we set here) and
	// after the --env appends. We first scrub any inherited ANTHROPIC_* / token /
	// auto-compact entries so the GLM vars are the SOLE occurrence (Linux getenv
	// returns the FIRST duplicate, so a stale ANTHROPIC_API_KEY would otherwise
	// shadow the GLM ANTHROPIC_AUTH_TOKEN). The token is resolved here, in the
	// agent, and lives ONLY on this child's c.Env — never in argv, the --env
	// transport, or any log.
	if *provider == "glm" {
		env = filterOutEnvKeys(env, glmConflictEnvKeys)
		glmEnv, gerr := providerEnvVars(*dataDir)
		if gerr != nil {
			// Static message only — never print the env/token.
			log.Fatalf("glm provider selected but no GLM key configured")
		}
		env = append(env, glmEnv...)
	}

	// A direct Claude/Codex/Gemini/Muse pane child may be a node script under
	// nvm/asdf/Volta; prepend its own bin directory at the one seam both the
	// pipe and PTY starts share, after every other environment builder.
	env = providerChildEnvForCommand(args[0], env)
	if !*noPty && runtime.GOOS != "windows" && *dataDir != "" &&
		!strings.HasSuffix(strings.ToLower(filepath.Base(args[0])), ".exe") {
		// PATH catches zsh/fish and other Unix shells; Bash also receives an
		// exported function because common version managers prepend PATH in
		// shell rc files. Keep Windows interop executables on their own PATH.
		if shimDir, err := ensureCodexInlineShim(*dataDir); err == nil {
			env = prependPathDir(env, shimDir)
			env = append(env, codexInlineShimEnvKey+"="+shimDir)
		} else {
			log.Printf("codex inline shim unavailable: %v", err)
		}
	}
	if !*noPty && runtime.GOOS != "windows" && *dataDir != "" &&
		strings.EqualFold(filepath.Base(args[0]), "zsh") {
		// zsh startup files can move a Codex install ahead of our PATH shim.
		// Source those files in their normal order, then install the pane-local
		// function after .zshrc has finished changing PATH.
		zshEnv, err := codexInlineZshEnvVars(*dataDir, env)
		if err == nil {
			env = append(env, zshEnv...)
		} else {
			log.Printf("codex inline zsh setup unavailable: %v", err)
		}
	}

	// Spawn the child either attached to a PTY (terminal panes) or wired
	// to plain pipes (--no-pty: headless stream-json agents that refuse a
	// TTY stdin). Both produce a childIO plus the child's *os.Process and a
	// wait func, so the rest of runAgent is mode-agnostic.
	var (
		cio       childIO
		proc      *os.Process
		waitFn    func() error
		waitState func() *os.ProcessState // waitFn's command: go-pty on Windows reports the status only there
	)
	if *noPty {
		// Pipe mode. Child stdin <- inW (we write); child stdout+stderr ->
		// outR (we read). stderr is merged into the data stream so a
		// startup error (e.g. bad flags) reaches the daemon instead of
		// vanishing. The child gets its OWN process group
		// (pipeChildSysProcAttr) so terminateChildTree's group signal hits
		// just the child — matching the PTY path's setsid.
		inR, inW, perr := os.Pipe()
		if perr != nil {
			log.Fatalf("stdin pipe: %v", perr)
		}
		outR, outW, perr := os.Pipe()
		if perr != nil {
			log.Fatalf("stdout pipe: %v", perr)
		}
		c := exec.Command(args[0], args[1:]...)
		if *cwd != "" {
			c.Dir = *cwd
		}
		c.Env = env
		c.Stdin = inR
		c.Stdout = outW
		c.Stderr = outW
		c.SysProcAttr = pipeChildSysProcAttr()
		if err := startWithoutCoreDumps(c); err != nil {
			log.Fatalf("pipe start: %v", err)
		}
		// The child holds its own dups; drop the parent's copies of the
		// child-side ends so EOF propagates when the child exits.
		_ = inR.Close()
		_ = outW.Close()
		cio = &pipeIO{r: outR, w: inW}
		proc = c.Process
		waitFn = c.Wait
		waitState = func() *os.ProcessState { return c.ProcessState }
	} else {
		// PTY mode. go-pty's Pty is an io.ReadWriteCloser that also exposes
		// Resize; its Command type is required because on Windows an
		// attached-to-console child needs ConPTY-specific handling (see
		// https://github.com/golang/go/issues/62708).
		ppty, perr := gopty.New()
		if perr != nil {
			log.Fatalf("pty new: %v", perr)
		}
		c := ppty.Command(args[0], args[1:]...)
		if *cwd != "" {
			c.Dir = *cwd
		}
		c.Env = env
		// Size the PTY BEFORE starting the child so its very first frame is
		// painted at the real spawn width. go-pty opens the pty (Unix) /
		// pseudo-console (Windows) in New(), so Resize here sets TIOCSWINSZ /
		// ResizePseudoConsole on an already-valid handle and the child
		// inherits it at exec. Resizing AFTER Start left a brief 0x0->80
		// (Unix) / 80x25 (Windows) window in which a fast-painting TUI could
		// commit an 80-col first frame that then never reflows when the real
		// size lands — a hard-wrapped narrow band pinned to the top of
		// scrollback.
		_ = ppty.Resize(int(*cols), int(*rows))
		if err := startWithoutCoreDumps(c); err != nil {
			log.Fatalf("pty start: %v", err)
		}
		cio = ppty
		proc = c.Process
		waitFn = c.Wait
		waitState = func() *os.ProcessState { return c.ProcessState }
	}
	defer cio.Close()

	// The agent inherits the daemon environment but has its own lower memory
	// thresholds. Existing agents launched without --data-dir fall back to the
	// same per-user default so their on-disk evidence still has a home.
	ctx, cancel := context.WithCancel(context.Background())
	// Exit state is declared before the guard so hard-limit teardown can wait
	// for the normal waitFn broadcaster, not merely the PTY reader's earlier
	// ctx cancellation.
	var childExited atomic.Bool
	var exitMsgPtr atomic.Pointer[[]byte]
	guardDataDir := *dataDir
	if guardDataDir == "" {
		guardDataDir = defaultDataDir()
	}
	var hardExitCode atomic.Int32
	memCfg := agentMemGuardConfig(guardDataDir)
	memCfg.exitFn = func(code int) {
		// Follow the normal child teardown so the wait goroutine broadcasts
		// FrameExit and cancels ctx before the accept loop returns. Bound both
		// waits: at the hard limit the wrapper itself must still terminate if a
		// wedged child refuses graceful and forced teardown.
		if proc != nil {
			_ = terminateChildTree(proc)
		}
		waitForChildExit := func(timeout time.Duration) bool {
			deadline := time.Now().Add(timeout)
			for time.Now().Before(deadline) {
				if childExited.Load() {
					return true
				}
				time.Sleep(10 * time.Millisecond)
			}
			return childExited.Load()
		}
		if !waitForChildExit(2 * time.Second) {
			if proc != nil {
				_ = killChildTree(proc)
			}
			_ = waitForChildExit(2 * time.Second)
		}
		if childExited.Load() {
			// childExited is published before FrameExit; ctx is canceled after
			// the broadcast completes, so wait briefly for that final handoff.
			select {
			case <-ctx.Done():
			case <-time.After(500 * time.Millisecond):
			}
		}
		hardExitCode.Store(int32(code))
		closeActiveListener()
	}
	if memCfg.softMB == 0 && memCfg.hardMB == 0 {
		log.Printf("[memguard] disabled role=agent (soft and hard thresholds are 0)")
	} else {
		log.Printf("[memguard] enabled role=agent soft=%dMB hard=%dMB", memCfg.softMB, memCfg.hardMB)
	}
	startMemGuard(ctx, memCfg)

	// OS-specific agent setup. No-op on Unix (daemon Setsid'd us);
	// on Windows, creates a Job Object with KILL_ON_JOB_CLOSE and
	// assigns us to it so our child dies cleanly when we do.
	// Non-fatal — the agent works without it, just loses guaranteed
	// grandchild cleanup on abrupt termination.
	if err := initAgentProcess(); err != nil {
		log.Printf("agent: initAgentProcess: %v (continuing)", err)
	}

	buffer := NewRingBuffer(ringBufferBytes)

	// agentGrid is a continuously-fed terminal-cell model owned by the
	// agent process. Its purpose is reattach correctness: when the daemon
	// restarts (auto-update) and reconnects to this still-running agent,
	// the daemon's own emulators allocated in AttachExisting start empty
	// and cannot reconstruct the screen from the ringbuf tail alone —
	// Codex normal-buffer renders cursor-positioned diffs against
	// scrollback cells that were evicted from the 8 MiB ring before the
	// snapshot cut. agentGrid never resets across daemon restarts (the
	// agent is the long-lived process), so its Snapshot at any moment is
	// the authoritative view of what Codex believes the screen looks like.
	// We serialise it on each new client connect and ship it as
	// FrameSyntheticPaint so the daemon (and ultimately xterm) get a
	// clear+repaint that overrides any garbage the raw replay produced.
	agentGrid := grid.New(int(*cols), int(*rows))
	defer agentGrid.Close()

	// Serialises writes to the CHILD's stdin (cio.Write / cio.Resize) across the
	// per-connection handleAgentClient goroutines. The agent multiplexes N daemon
	// connections onto ONE shared cio, and during a daemon auto-update there is a
	// ≥600ms window where BOTH the predecessor and successor daemon hold a live
	// connection (updater: the successor reattaches before the predecessor exits).
	// Each daemon serialises its OWN writes (per-pane agentWriteMu) but NOT across
	// the two processes — so without this lock two FrameData payloads can interleave
	// at the child's stdin pipe (a native pane's stdin is a real os.Pipe; a write
	// > PIPE_BUF is non-atomic), splicing one JSON line into another. `claude -p
	// --input-format stream-json` then reads a corrupt NDJSON line and self-exits
	// code 1 — the "Session ended on the first message after an update" bug. The
	// lock makes each frame's payload atomic w.r.t. every other connection.
	var cioWriteMu sync.Mutex

	// Subscriber fan-out.
	var subsMu sync.Mutex
	// See agentFanout: PTY connections read the output ring by position so a
	// burst never drops bytes; no-PTY connections take backpressure.
	fan := newAgentFanout(buffer, *noPty)
	var retirement *ownerAgentRetirement
	if *ownerRetirementPane != "" && *ownerRetirementPane == ownerRetirementPaneFromEnv(env) && !*noPty {
		retirement = &ownerAgentRetirement{paneID: *ownerRetirementPane, inputMu: &cioWriteMu, connections: func() int { subsMu.Lock(); defer subsMu.Unlock(); return fan.countLocked() }, connectionLive: func(conn net.Conn) bool {
			subsMu.Lock()
			defer subsMu.Unlock()
			uc, ok := conn.(*net.UnixConn)
			if !ok {
				return false
			}
			return fan.hasLocked(uc)
		}}
	}

	// curDims tracks the PTY's live dimensions (cols<<16 | rows), seeded
	// from the spawn flags and updated on every applied FrameResize. Each
	// new daemon connection is told these dims FIRST (FrameDims) so a
	// restarted daemon adopts the truth instead of its stale persisted
	// copy — the agent is the only process that survives daemon restarts
	// and therefore the only source of truth for the PTY size.
	var curDims atomic.Uint64
	curDims.Store(uint64(*cols)<<16 | uint64(*rows)&0xffff)

	addSub := func(conn *net.UnixConn) (chan []byte, []byte, []byte, []byte) {
		// Connection admission and commit use the same coordinator lock.
		// A new daemon cannot slip between the final count and the close.
		if retirement != nil {
			retirement.mu.Lock()
			retirement.inputSequence++
			retirement.releaseLocked()
			defer retirement.mu.Unlock()
		}
		subsMu.Lock()
		snapshot := buffer.Snapshot()
		var paint []byte
		// Take the grid snapshot under the same subsMu that serialises
		// PTY-byte writes (buffer.Write + agentGrid.Feed). The paint
		// reflects the same byte-stream cut as the ringbuf snapshot, so
		// when the daemon receives [replay bytes ... synthetic paint],
		// the paint matches what Codex believes the screen is at the
		// instant the replay ends.
		if gs := agentGrid.Snapshot(); gridSnapshotHasText(gs) {
			paint = serializeGridSnapshot(gs, -1)
		}
		ch := fan.addLocked(conn)
		subsMu.Unlock()
		d := curDims.Load()
		dims, _ := json.Marshal(map[string]uint16{
			"cols": uint16(d >> 16), "rows": uint16(d & 0xffff),
		})
		return ch, snapshot, paint, dims
	}
	removeSub := func(conn *net.UnixConn) {
		subsMu.Lock()
		fan.removeLocked(conn)
		subsMu.Unlock()
	}
	// resizeAgentGrid keeps the agent's authoritative cell model in sync
	// with the PTY's window size whenever a client sends FrameResize. The
	// grid emulator's Resize is internally locked, so no subsMu needed.
	// Also records the dims so the next daemon (re)attach is told the
	// truth via FrameDims.
	resizeAgentGrid := func(cols, rows int) {
		if cols > 0 && rows > 0 {
			agentGrid.Resize(cols, rows)
			curDims.Store(uint64(cols)<<16 | uint64(rows)&0xffff)
		}
	}
	fanoutLocked := fan.fanoutLocked

	// PTY read loop.
	go func() {
		buf := make([]byte, 32*1024)
		for {
			n, err := cio.Read(buf)
			if n > 0 {
				chunk := make([]byte, n)
				copy(chunk, buf[:n])
				subsMu.Lock()
				buffer.Write(chunk)
				// Feed under subsMu so addSub's (buffer, grid)
				// snapshot pair is consistent with this byte cut.
				// DrainReplies discards any cursor-position / DA /
				// device-attribute responses the emulator generates
				// — the real PTY child is already answering those
				// queries via the live PTY pipe; we just keep e.out
				// from growing unbounded.
				//
				// Skip it entirely for --no-pty (native/headless) panes:
				// they carry JSONL, not terminal output, so VT-emulating
				// it is pure waste — and it runs HERE under subsMu on every
				// chunk, lengthening the lock hold that addSub/fanout
				// contend for, across every concurrent native pane. The
				// grid's only consumer is the synthetic-paint reattach
				// repair for terminal/Codex panes; a native pane rebuilds
				// from its NativeEvent re-seed on reconnect and never reads
				// the paint (the daemon likewise skips its VT models for
				// native panes via the `if p.Kind == "native"` readLoop
				// branch in pane.go). An unfed grid stays empty, so addSub
				// ships no paint for native panes.
				if !*noPty {
					agentGrid.Feed(chunk)
					_ = agentGrid.DrainReplies()
				}
				fanoutLocked(chunk)
				subsMu.Unlock()
			}
			if err != nil {
				cancel()
				return
			}
		}
	}()

	// Wait for child to exit, broadcast exit, close everything.
	go func() {
		err := waitFn()
		code := exitCodeFromWait(err, waitState())
		msg, _ := json.Marshal(map[string]int{"code": code})
		// Publish exit state BEFORE broadcasting so a new connection
		// arriving during the broadcast sees childExited=true and
		// gets FrameExit via handleAgentClient's late-arrival path.
		msgCopy := append([]byte(nil), msg...)
		exitMsgPtr.Store(&msgCopy)
		childExited.Store(true)

		// Detach under the subscription lock, then frame the exit outside it.
		// A slow socket must not block the retirement timer's connection check.
		subsMu.Lock()
		exitedConnections, waitPumps := fan.detachAllLocked(2 * time.Second)
		subsMu.Unlock()
		// Let each pump hand its last bytes to the writer before FrameExit so
		// the final output isn't cut off. Bounded: a stuck socket must not
		// hold up the exit broadcast.
		waitPumps()
		for _, conn := range exitedConnections {
			if retirement != nil {
				retirement.outputMu.Lock()
			}
			_ = WriteFrame(conn, FrameExit, msg)
			_ = conn.Close()
			if retirement != nil {
				retirement.outputMu.Unlock()
			}
		}
		cancel()
	}()

	// Forward SIGTERM/SIGINT (Ctrl+C / Ctrl+Break on Windows) to the
	// child's process tree. Unix uses the negative-pid group signal
	// trick; Windows rides on the Job Object cleanup when this
	// process exits after the goroutine returns.
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGTERM, syscall.SIGINT)
	go func() {
		<-sigCh
		if proc != nil {
			_ = terminateChildTree(proc)
		}
	}()

	// Shut down the listener after a short grace window when the child
	// exits. During the grace window, late-arriving clients still get
	// a proper FrameExit via handleAgentClient's childExited check.
	go func() {
		<-ctx.Done()
		time.Sleep(exitLingerDuration)
		closeActiveListener()
	}()

	// Socket self-heal watchdog: if our socket FILE is unlinked out from under
	// us while the child is still running, re-create the listener at the same
	// path so a (re)connecting daemon can still dial us instead of killing us.
	// The live child is never touched. Stops at ctx cancel (child exit) so it
	// never races the grace-close above or resurrects the socket on the way out.
	go func() {
		ticker := time.NewTicker(socketRebindCheckInterval)
		defer ticker.Stop()
		for {
			select {
			case <-ctx.Done():
				return
			case <-ticker.C:
				if _, statErr := os.Stat(*socketPath); statErr == nil {
					continue // still present
				} else if !os.IsNotExist(statErr) {
					continue // transient stat error — don't thrash
				}
				newLn, lerr := net.Listen("unix", *socketPath)
				if lerr != nil {
					// Lost the race (something else just bound the path) or a
					// transient failure — try again next tick.
					continue
				}
				_ = os.Chmod(*socketPath, 0o600)
				lnMu.Lock()
				if shuttingDown {
					lnMu.Unlock()
					_ = newLn.Close() // we're exiting; don't resurrect the socket
					return
				}
				old := activeLn
				activeLn = newLn
				lnMu.Unlock()
				// Closing the old listener unblocks the accept loop so it swaps to
				// newLn. CRITICAL: a *net.UnixListener unlinks its socket path on
				// Close by default — but newLn just created the file at that SAME
				// path, so a plain old.Close() deletes the very socket we just
				// re-bound, leaving us unreachable again (the exact bug this
				// watchdog exists to prevent). Disable unlink-on-close on the old
				// listener so only newLn owns the path.
				if ul, ok := old.(*net.UnixListener); ok {
					ul.SetUnlinkOnClose(false)
				}
				_ = old.Close()
				log.Printf("agent: socket %s was unlinked while alive; re-bound to stay reachable", *socketPath)
			}
		}
	}()

	// Accept loop. Re-reads activeLn each iteration so a watchdog re-bind
	// (socket self-heal) seamlessly swaps the listener under us. An Accept
	// error that is NEITHER a deliberate swap NOR shutdown ends the loop as
	// before.
	for {
		lnMu.Lock()
		acceptLn := activeLn
		lnMu.Unlock()
		conn, err := acceptLn.Accept()
		if err != nil {
			lnMu.Lock()
			done := shuttingDown
			swapped := activeLn != acceptLn
			lnMu.Unlock()
			if done {
				break
			}
			if swapped {
				continue // watchdog installed a fresh listener; accept on it
			}
			break // unexpected error on the live listener — exit as before
		}
		uc := conn.(*net.UnixConn)
		go handleAgentClient(uc, cio, &cioWriteMu, addSub, removeSub, resizeAgentGrid, proc, &childExited, &exitMsgPtr, retirement)
	}

	// Ensure child is gone.
	if proc != nil {
		_ = killChildTree(proc)
	}
	return int(hardExitCode.Load())
}

// writeChildLocked writes one frame payload to the child's stdin while holding
// `mu`, so concurrent handleAgentClient goroutines (e.g. the predecessor +
// successor daemon during an auto-update overlap) can't interleave their bytes at
// the pipe. The whole payload goes out atomically w.r.t. any other locked writer;
// since each native input frame is one `\n`-terminated NDJSON line, this keeps the
// child's stdin a clean sequence of whole lines.
func writeChildLocked(mu *sync.Mutex, cio childIO, payload []byte) error {
	mu.Lock()
	defer mu.Unlock()
	_, err := cio.Write(payload)
	return err
}

func handleAgentClient(
	conn *net.UnixConn,
	cio childIO,
	cioWriteMu *sync.Mutex,
	addSub func(*net.UnixConn) (chan []byte, []byte, []byte, []byte),
	removeSub func(*net.UnixConn),
	resizeGrid func(cols, rows int),
	killProc *os.Process,
	childExited *atomic.Bool,
	exitMsgPtr *atomic.Pointer[[]byte],
	retirements ...*ownerAgentRetirement,
) {
	ch, snapshot, paint, dims := addSub(conn)
	var retirement *ownerAgentRetirement
	if len(retirements) > 0 {
		retirement = retirements[0]
	}
	if retirement != nil {
		retirement.attached()
		defer retirement.abort(conn, "")
	}
	frameWriteMu := &sync.Mutex{}
	if retirement != nil {
		frameWriteMu = &retirement.outputMu
	}
	writeReply := func(reply ownerRetirementReply) {
		raw, _ := json.Marshal(reply)
		frameWriteMu.Lock()
		defer frameWriteMu.Unlock()
		_ = WriteFrame(conn, FrameOwnerRetireReply, raw)
	}
	var removeOnce sync.Once
	remove := func() {
		removeOnce.Do(func() {
			removeSub(conn)
		})
	}
	defer conn.Close()
	defer remove()

	// Dims first: a restarted daemon rebuilt this pane from stale persisted
	// dims — it must adopt the PTY's real size BEFORE consuming the replay,
	// so its emulators are sized right and /api/panes never serves the lie
	// back to reconnecting clients. Old daemons drop the unknown frame.
	frameWriteMu.Lock()
	_ = WriteFrame(conn, FrameDims, dims)
	info, _ := json.Marshal(struct {
		Version    string `json:"version"`
		PID        int    `json:"pid"`
		Proto      int    `json:"proto"`
		Retirement bool   `json:"ownerRetirement,omitempty"`
	}{Version: version, PID: os.Getpid(), Proto: agentProtoVersion, Retirement: retirement != nil})
	_ = WriteFrame(conn, FrameAgentInfo, info)

	// Send the replay buffer so the client can redraw the terminal, then
	// (for Codex normal-buffer panes whose ringbuf tail is diff-only) a
	// synthetic paint built from the agent's authoritative grid model.
	// The paint clears + repaints the visible screen, repairing whatever
	// the diff replay produced. FrameReplayEnd fires AFTER both, so the
	// daemon's emitCodexReplayRepair sees the now-correct emulator state.
	_ = writeReplayWithPaint(conn, snapshot, paint)
	frameWriteMu.Unlock()

	// Late-arrival path: if the child already exited before this
	// connection, send the cached FrameExit and disconnect cleanly.
	// Without this, a fast-exiting command (e.g. `echo hi`) races the
	// daemon's dial retry and the whole spawn fails with "no such
	// file or directory" because socket teardown wins.
	if childExited.Load() {
		if m := exitMsgPtr.Load(); m != nil {
			frameWriteMu.Lock()
			_ = WriteFrame(conn, FrameExit, *m)
			frameWriteMu.Unlock()
		}
		return
	}

	// Writer: PTY fanout → socket
	done := make(chan struct{})
	go func() {
		defer close(done)
		for chunk := range ch {
			frameWriteMu.Lock()
			err := WriteFrame(conn, FrameData, chunk)
			frameWriteMu.Unlock()
			if err != nil {
				// Wake the reader so it removes/closes this subscription. Keep
				// draining until then: a no-PTY fanout may be synchronously
				// backpressured on this channel while holding subsMu, and an
				// immediate return here would deadlock removal behind that lock.
				_ = conn.Close()
				for range ch {
				}
				return
			}
		}
	}()

	// Reader: socket → PTY
	for {
		t, payload, err := ReadFrame(conn)
		if err != nil {
			break
		}
		switch t {
		case FrameData:
			if retirement != nil {
				retirement.input(payload)
			}
			// Serialised against every other connection's stdin write (and resize)
			// so one frame's payload lands atomically — no interleave with a
			// concurrent write from the predecessor/successor daemon during a swap.
			werr := writeChildLocked(cioWriteMu, cio, payload)
			if retirement != nil {
				retirement.inputDone()
			}
			if werr != nil {
				goto end
			}
		case FrameResize:
			if retirement != nil {
				retirement.attached()
			}
			var rs struct {
				Cols uint16 `json:"cols"`
				Rows uint16 `json:"rows"`
			}
			if json.Unmarshal(payload, &rs) == nil && rs.Cols > 0 && rs.Rows > 0 {
				cioWriteMu.Lock()
				_ = cio.Resize(int(rs.Cols), int(rs.Rows))
				cioWriteMu.Unlock()
				resizeGrid(int(rs.Cols), int(rs.Rows))
			}
		case FrameOwnerRetirePrepare:
			var req ownerRetirementRequest
			if retirement == nil {
				writeReply(ownerRetirementReply{Error: "conditional retirement unsupported"})
				continue
			}
			if len(payload) > 4096 || json.Unmarshal(payload, &req) != nil {
				continue
			}
			// The ordered frame is the input barrier; do not block the reader on
			// filesystem proof. Later input cancels the lease before normal delivery.
			sequence := retirement.sequence()
			go func() { writeReply(retirement.prepare(conn, req, sequence)) }()
		case FrameOwnerRetireCommit, FrameOwnerRetireAbort:
			var req ownerRetirementRequest
			if retirement == nil || len(payload) > 4096 || json.Unmarshal(payload, &req) != nil {
				continue
			}
			if t == FrameOwnerRetireAbort {
				retirement.abort(conn, req.Token)
			} else {
				// Accepted commit acknowledgement precedes FrameExit. The
				// child waiter uses this same output lock after detaching.
				frameWriteMu.Lock()
				reply := retirement.commit(conn, req.Token)
				raw, _ := json.Marshal(reply)
				_ = WriteFrame(conn, FrameOwnerRetireReply, raw)
				frameWriteMu.Unlock()
			}
		case FrameKillRequest:
			if retirement != nil {
				retirement.abort(conn, "")
			}
			if killProc != nil {
				_ = terminateChildTree(killProc)
				go func() {
					time.Sleep(2 * time.Second)
					if killProc != nil {
						_ = killChildTree(killProc)
					}
				}()
			}
		}
	}
end:
	_ = conn.Close()
	remove()
	<-done
}

// childSessionEnvKey is the env var Claude Code sets in a NESTED child
// session. Its PRESENCE in a live `claude`'s environ means that claude
// inherited the dirty launch env and will never write its own transcript —
// the unambiguous marker of a "degraded" pane (a genuine top-level claude
// sets its own SESSION_ID but never CHILD_SESSION). Used by the degraded-pane
// detector and the daemon self-clean re-exec guard.
const childSessionEnvKey = "CLAUDE_CODE_CHILD_SESSION"

// stripInheritedClaudeEnv removes Claude Code's session-context environment
// variables (the "CLAUDE_CODE_*" family and the CLAUDECODE marker) from a
// process environment. We apply it to every pane command's env.
//
// Why: if the daemon itself was launched from inside a Claude Code session,
// CLAUDE_CODE_SESSION_ID + CLAUDE_CODE_CHILD_SESSION are inherited and leak
// into the panes we spawn. A `claude` started with those set runs as a NESTED
// child session of the launching conversation and never writes its own
// transcript — so the pane's conversation is unreadable (empty Activity tab).
// Panes are independent top-level terminals; a genuine `claude` invocation in
// the pane sets these itself. ANTHROPIC_*/credential vars are intentionally
// left untouched.
func stripInheritedClaudeEnv(env []string) []string {
	out := make([]string, 0, len(env))
	for _, kv := range env {
		key := kv
		if i := strings.IndexByte(kv, '='); i >= 0 {
			key = kv[:i]
		}
		if key == "CLAUDECODE" || strings.HasPrefix(key, "CLAUDE_CODE_") {
			continue
		}
		out = append(out, kv)
	}
	return out
}

// ensureLocalBinOnPath prepends $HOME/.local/bin to PATH unless it's already an
// element, mutating the env slice's PATH entry in place. That dir is where the
// native Claude installer (claude.ai/install.sh) drops the `claude` binary; a
// freshly spawned shell pane otherwise only sees the daemon's slim inherited
// PATH, so `claude` typed in a shell would 404 even right after installing it.
// Prepend (not append) matches loginShellInit's ordering for wrapped command
// panes, so resolution is consistent across shell and `claude` panes. Idempotent
// and a no-op when $HOME is unknown or PATH is absent-and-uncreatable.
func ensureLocalBinOnPath(env []string) []string {
	home := ""
	for _, kv := range env {
		if strings.HasPrefix(kv, "HOME=") {
			home = strings.TrimPrefix(kv, "HOME=")
			break
		}
	}
	if home == "" {
		if h, err := os.UserHomeDir(); err == nil {
			home = h
		}
	}
	if home == "" {
		return env
	}
	localBin := filepath.Join(home, ".local", "bin")
	sep := string(os.PathListSeparator)
	for i, kv := range env {
		if !strings.HasPrefix(kv, "PATH=") {
			continue
		}
		cur := strings.TrimPrefix(kv, "PATH=")
		for _, p := range strings.Split(cur, sep) {
			if p == localBin {
				return env // already present — don't duplicate or reorder
			}
		}
		if cur == "" {
			env[i] = "PATH=" + localBin
		} else {
			env[i] = "PATH=" + localBin + sep + cur
		}
		return env
	}
	// No PATH entry at all (unusual): introduce one so ~/.local/bin still wins.
	return append(env, "PATH="+localBin)
}

func ensureKnownWindowsCliDirsOnPath(env []string, childCmd string) []string {
	sep, ok := windowsChildPathSeparator(childCmd)
	if !ok {
		return env
	}
	dirs := knownWindowsCliDirs(env)
	return prependDirsOnPath(env, dirs, sep, true)
}

func windowsChildPathSeparator(childCmd string) (string, bool) {
	if os.PathListSeparator == ';' {
		return ";", true
	}
	if isWindowsChildCommand(childCmd) {
		return ";", true
	}
	return "", false
}

func knownWindowsCliDirs(env []string) []string {
	var dirs []string
	localAppData := envValueFromList(env, "LOCALAPPDATA")
	if localAppData == "" {
		if userProfile := envValueFromList(env, "USERPROFILE"); userProfile != "" {
			localAppData = joinWindowsPath(userProfile, "AppData", "Local")
		}
	}
	if localAppData != "" {
		codexBin := joinWindowsPath(localAppData, "Programs", "OpenAI", "Codex", "bin")
		if dirExistsForHost(codexBin) {
			dirs = append(dirs, codexBin)
		}
	}

	// WSL daemon launching a Windows shell: the Linux environment often lacks
	// LOCALAPPDATA/USERPROFILE, but the Windows user install is still visible
	// through /mnt/c. Add the Windows-form path because pwsh.exe consumes it.
	if os.PathListSeparator != ';' && isInsideWSL() {
		matches, _ := filepath.Glob("/mnt/c/Users/*/AppData/Local/Programs/OpenAI/Codex/bin")
		for _, m := range matches {
			if fi, err := os.Stat(m); err == nil && fi.IsDir() {
				dirs = append(dirs, hostPathToWindowsPath(m))
			}
		}
	}
	return dirs
}

func prependDirsOnPath(env []string, dirs []string, sep string, caseInsensitive bool) []string {
	if len(dirs) == 0 {
		return env
	}
	key := "PATH"
	cur := ""
	found := false
	out := make([]string, 0, len(env))
	for _, kv := range env {
		eq := strings.IndexByte(kv, '=')
		if eq < 0 {
			out = append(out, kv)
			continue
		}
		k := kv[:eq]
		matches := k == "PATH"
		if caseInsensitive {
			matches = strings.EqualFold(k, "PATH")
		}
		if matches {
			if !found {
				key = k
				found = true
			}
			if cur == "" {
				cur = kv[eq+1:]
			} else if kv[eq+1:] != "" {
				cur += sep + kv[eq+1:]
			}
			continue
		}
		out = append(out, kv)
	}
	// Duplicate PATH case variants are intentionally removed above. On Windows,
	// Go/exec resolves duplicate env keys case-insensitively and the last entry
	// wins; leaving a later stale `PATH` can silently override the fixed `Path`.

	seen := make(map[string]bool)
	var merged []string
	add := func(dir string) {
		dir = strings.TrimSpace(dir)
		if dir == "" {
			return
		}
		k := strings.TrimRight(dir, `\/`)
		if caseInsensitive {
			k = strings.ToLower(k)
		}
		if seen[k] {
			return
		}
		seen[k] = true
		merged = append(merged, dir)
	}
	for _, dir := range dirs {
		add(dir)
	}
	for _, dir := range strings.Split(cur, sep) {
		add(dir)
	}

	kv := key + "=" + strings.Join(merged, sep)
	return append(out, kv)
}

func isWindowsChildCommand(cmd string) bool {
	cmd = strings.TrimSpace(cmd)
	if cmd == "" {
		return false
	}
	lower := strings.ToLower(strings.ReplaceAll(cmd, `\`, `/`))
	base := lower
	if slash := strings.LastIndexByte(base, '/'); slash >= 0 {
		base = base[slash+1:]
	}
	switch base {
	case "pwsh.exe", "powershell.exe", "cmd.exe":
		return true
	}
	return strings.HasSuffix(base, ".exe") && (strings.HasPrefix(lower, "/mnt/") || strings.Contains(lower, ":/"))
}

func joinWindowsPath(base string, elems ...string) string {
	base = strings.TrimRight(base, `\/`)
	for _, elem := range elems {
		elem = strings.Trim(elem, `\/`)
		if elem == "" {
			continue
		}
		if base == "" {
			base = elem
		} else {
			base += `\` + elem
		}
	}
	return base
}

func dirExistsForHost(path string) bool {
	hostPath := windowsPathToHostPath(path)
	fi, err := os.Stat(hostPath)
	return err == nil && fi.IsDir()
}

func windowsPathToHostPath(path string) string {
	if os.PathListSeparator == ';' {
		return path
	}
	p := strings.ReplaceAll(path, `\`, `/`)
	if len(p) >= 3 && p[1] == ':' && p[2] == '/' {
		drive := strings.ToLower(p[:1])
		rest := strings.TrimLeft(p[3:], `/`)
		if rest == "" {
			return "/mnt/" + drive
		}
		return "/mnt/" + drive + "/" + rest
	}
	return path
}

func hostPathToWindowsPath(path string) string {
	p := strings.ReplaceAll(path, `\`, `/`)
	if len(p) >= len("/mnt/c") && strings.HasPrefix(strings.ToLower(p), "/mnt/") {
		if len(p) > len("/mnt/c") && p[6] != '/' {
			return path
		}
		drive := strings.ToUpper(p[5:6])
		rest := ""
		if len(p) > len("/mnt/c") {
			rest = strings.TrimLeft(p[6:], `/`)
		}
		if rest == "" {
			return drive + `:\`
		}
		return drive + `:\` + strings.ReplaceAll(rest, `/`, `\`)
	}
	return path
}

func envValueFromList(env []string, key string) string {
	for _, kv := range env {
		eq := strings.IndexByte(kv, '=')
		if eq < 0 {
			continue
		}
		if strings.EqualFold(kv[:eq], key) {
			return kv[eq+1:]
		}
	}
	return ""
}

// exitCodeFromWait is the exit status of the pane's child once Wait has
// returned. On Unix and in pipe mode Wait returns an *exec.ExitError; on
// Windows, go-pty's ConPTY command leaves the status only in the command's
// ProcessState, so read that too. A nil error without a state is success;
// any other error is -1.
func exitCodeFromWait(err error, state *os.ProcessState) int {
	if ee, ok := err.(*exec.ExitError); ok {
		return ee.ExitCode()
	}
	if state != nil {
		return state.ExitCode()
	}
	if err == nil {
		return 0
	}
	return -1
}
