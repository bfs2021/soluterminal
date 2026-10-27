import { terminalRetirementViewerId } from '../lib/terminalRetirementViewer';
import { notePaneTyped, paneDictating, usePaneDictation } from '../extensions';
import { PreservedTerminalInput } from './PreservedTerminalInput';
import { abandonTerminalRetirement, beginTerminalInteraction, beginTerminalRetirement, cancelTerminalRetirement, holdTerminalInput, releaseTerminalRetirement, terminalHasPendingInteraction, terminalRecoveredInput, terminalInputAllowed, useTerminalRetirementPaused } from '../lib/terminalInteractionState';
import { quickReplyHasPendingInteraction } from '../lib/quickReplyDrafts';
import { currentRoutingScope, routingPrincipalEpoch, routingPrincipalAllowed, signStreamUrl, streamSigningNeeded } from '../api';
import { effectiveVisiblePaneIds, effectiveTerminalTarget } from '../store';
import { ensureTerminalSession, registerTerminalCloseGuard, registerSessionKeepalive, captureSessionGesture, sessionVisible, processIdentity, type TerminalViewSession } from '../lib/terminalViewSessions';
import { useCallback, useEffect, useMemo, useRef, useState, type CSSProperties } from 'react';
import { Terminal } from '@xterm/xterm';
import { FitAddon } from '@xterm/addon-fit';
import { WebLinksAddon } from '@xterm/addon-web-links';
import { isEmbedded, openEmbedUrl } from '../embed';
import { openTerminalFileLink } from '../terminalFileLink';
import { SearchAddon } from '@xterm/addon-search';
import '@xterm/xterm/css/xterm.css';
import { api } from '../api';
import { openWebSocket, privateRelaySocketsFor } from '../lib/signedStreams';
import { debugLog, lifecycleLog } from '../debug';
import { recordIme } from '../imeTrace';
import { isMobileViewport } from '../lib/mobile';
import { resolveTerminalTheme, useStore } from '../store';
import { DRAG_MIME, computeZone, type DropZone } from '../lib/paneDnd';
import { collectPaneIds } from '../lib/layout';
import { computePaneRestoreTarget } from '../lib/paneRestoreFit';
import { newOscStripState, stripOscColorQueries } from '../lib/oscStrip';
import { ReplayAnswerGate } from '../lib/terminalReplies';
import { isTypingElsewhere } from '../lib/focusGuard';
import { userRecentlyActive } from '../lib/userActivity';
import { isPaneHostParked } from '../lib/paneHosts';
import { clearPaneRunningWork, setPaneRunningWork } from '../lib/paneWork';
import { roleConvertAllowed } from '../extensions';
import { operatorFeaturesAllowed } from '../entitlements';
import { restartPaneFlow } from '../lib/paneRestart';
import { applyTerminalTheme, TERMINAL_BACKGROUND_CSS_PROPERTY } from '../themes';
import type { PaneInfo } from '../types';
import { ApprovalActions } from './ApprovalActions';
import { logScrollDiag } from '../scrollDiag';
import { attachPaneImagePasteHandlers } from './paneImagePaste';
import { attachPaneMousePasteHandlers } from './paneMousePaste';
import { SwitchInterruptedBanner } from './native/NativeEventViews';
import { shouldShowSwitchNotice, switchNoticeKey } from '../native/modeSwitch';
import { PaneBodyOverlays } from './PaneBodyOverlays';
import { PaneFindBar } from './PaneFindBar';
import { PaneContextMenu } from './PaneContextMenu';
import { PaneFlagMemo } from './PaneFlagMemo';
import { PaneHeader } from './PaneHeader';
import { PaneLastPrompt } from './PaneLastPrompt';
import { useIsMobileView } from './useIsMobileView';
import { usePaneContextMenu } from './usePaneContextMenu';
import { usePaneFind } from './usePaneFind';
import { usePaneReaderMode } from './usePaneReaderMode';
import { useKeyboardInsetShift } from './useKeyboardInsetShift';
import { ContextPackDialog } from './ContextPackDialog';
import { PaneIdentityDialog } from './PaneIdentityDialog';
import { copyToClipboard } from '../lib/clipboard';
import { handleTerminalCopyKey } from '../lib/terminalClipboard';
import { paneUnread } from '../lib/turnChip';
import { planSelectionSend } from '../lib/selectionSend';
import { replayPinTarget } from '../lib/replayPin';

interface Props {
  pane: PaneInfo;
  paneIndex: number;
  session?: TerminalViewSession;
}

// Replays bigger than this get the catch-up veil. xterm parses writes in
// time-sliced chunks and paints intermediate states, so a large replay
// (cold mount after app start / daemon update, or a reconnect re-replay)
// is visible as seconds of fast-scrolling through the transcript before
// the pane settles at the latest content. The veil hides the catch-up
// and reveals the pane already settled. Small replays parse within a
// frame or two — no veil, no flicker.
const CATCHUP_VEIL_MIN_BYTES = 64 * 1024;

// Stable fallback for the lastPrompts selector — an inline `?? []`
// would mint a fresh array per call and trip useSyncExternalStore
// into an infinite re-render (React error #185).
const NO_PROMPTS: string[] = [];

// scrollbackForPaneCount scales xterm scrollback DOWN as the visible pane
// count grows — a memory/UX tradeoff. 20000 lines × N terminals is a lot of
// RAM when ~40 panes are open; shrinking trades scrollback HISTORY (oldest
// lines drop) for memory in big grids. We deliberately keep the common
// small-layout case at the current 20000 so the focused workflow is
// UNCHANGED, and we never exceed 20000. Conservative thresholds:
//   <=4 panes  → 20000 (unchanged — the focused / common case)
//   5–8 panes  → 12000
//   9–16 panes → 8000
//   >16 panes  → 5000
function scrollbackForPaneCount(count: number): number {
  if (count <= 4) return 20000;
  if (count <= 8) return 12000;
  if (count <= 16) return 8000;
  return 5000;
}

// Minimum columns a pane may report to its PTY / render in xterm. Claude
// Code's TUI lays out via cursor-move escape sequences; below ~40 cols the
// positioning breaks and words/rows misplace (the "8 panes garbles, 6 is
// fine" symptom — each pane just gets too narrow). This floor is a COMPLETE
// NO-OP for any pane already ≥ this width (every healthy 6-pane layout),
// so it can't disturb the well-tuned fit/resize plumbing. It only engages
// when a dense workspace shrinks a pane below readable width: xterm then
// renders MIN cols and the right edge clips (a legible left-aligned TUI
// beats garble). xterm and the PTY both see the floored cols, so they stay
// in sync — no desync. term.resize() doesn't change the host element, so
// ResizeObserver can't loop on it.
const MIN_PANE_COLS = 40;


export function Pane({ pane, paneIndex, session: suppliedSession }: Props) {
  const fallbackSession = useRef<TerminalViewSession>({key:JSON.stringify([currentRoutingScope().key,pane.id]),scope:currentRoutingScope(),principal:routingPrincipalEpoch(),pane,processIdentity:processIdentity(pane),generation:0,retained:false,invalid:false});
  const session = suppliedSession ?? fallbackSession.current;
  if (!suppliedSession) session.pane = pane;
  const key = session.key;
  const retirementPaused = useTerminalRetirementPaused(key);
  const recoveryKey = JSON.stringify([key, session.principal]);
  const canAct = () => sessionVisible(session) && effectiveVisiblePaneIds(useStore.getState()).includes(pane.id) && session.processIdentity === processIdentity(session.pane);
  const viewKind = useStore(s=>s.mainPresentation.kind);
  const renderedGeneration = useStore(s => s.navigationGeneration);
  const actionValid = () => renderedGeneration === useStore.getState().navigationGeneration && canAct() && terminalInputAllowed(key);
  const ownerPresentation = pane.role === 'task_owner' && viewKind === 'owner';
  // Host placement changes outside React. Re-evaluate the guarded header and
  // prompt strip after reattachment, even when metadata/history is unchanged.
  const [, setPlacementEpoch] = useState(0);
  const registered = useRef<Record<string,unknown>>({});
  const ownershipToken = useRef(Symbol(key));

  const hostRef = useRef<HTMLDivElement | null>(null);
  const termRef = useRef<Terminal | null>(null);
  const fontRefitRef = useRef<(() => void) | null>(null);
  // SearchAddon handle is lifted to a ref (vs. captured inside the
  // mount effect's closure) so the in-pane find overlay rendered at
  // the component's JSX can call into it — findNext/findPrevious from
  // a React event handler that runs after mount.
  const searchAddonRef = useRef<SearchAddon | null>(null);
  const wsRef = useRef<WebSocket | null>(null);
  // Holds the live WS-effect's connect() closure so the respawn-reconnect
  // backstop (a separate effect) can re-open the socket without re-running the
  // whole WS effect. Set inside the effect, cleared on its teardown.
  const connectRef = useRef<(() => void) | null>(null);
  const hasCodexRef = useRef(!!pane.hasCodex || !!pane.hasMuse);
  useEffect(() => {
    hasCodexRef.current = !!pane.hasCodex || !!pane.hasMuse;
  }, [pane.hasCodex, pane.hasMuse]);
  const setFocus = useStore((s) => s.setFocus);
  const focused = useStore((s) => effectiveTerminalTarget(s) === pane.id) && canAct();
  // Keep the focused pane's input row above the on-screen keyboard on mobile.
  // Normal-buffer TUIs (Codex) draw their input box at the BOTTOM rows, so we
  // resize the host to fit above the keyboard rather than translate it (which
  // would lift the input box off-screen). Alt-screen (Claude) keeps the
  // zero-flicker translate path. See the hook.
  useKeyboardInsetShift(hostRef, focused, !!pane.hasCodex || !!pane.hasMuse);
  const revealed = useStore((s) => s.recentlyRevealedPaneId === pane.id);
  // Dictation aimed at this pane (paneDictation slot, extensions.ts) —
  // pinned at recording-start so the glow and chip stay anchored to the
  // TARGET pane even if focus moves during recording or transcription.
  const dictation = usePaneDictation(pane.id);
  const dictating = dictation !== null;
  const dictationPhase = dictation?.phase ?? null;
  const dictationAboutToCancel = dictation?.aboutToCancel ?? false;
  const killPane = useStore((s) => s.killPane);
  const resumePane = useStore((s) => s.resumePane);
  const renamePane = async (_id:string,title:string)=>{
   const valid=captureSessionGesture(session);if(!valid())return;
   const saved=await api.renamePane(pane.id,title,session.scope);
   if(valid()) {ensureTerminalSession(session.scope,saved,session.retained);useStore.setState(s=>s.panes[pane.id]?.pid===saved.pid?{panes:{...s.panes,[pane.id]:saved}}:{});}
  };
  const switchPaneMode = useStore((s) => s.switchPaneMode);
  const applyPaneSnapshot=(changed:PaneInfo)=>{ensureTerminalSession(session.scope,changed,session.retained);useStore.setState(s=>s.panes[pane.id]?.pid===pane.pid?{panes:{...s.panes,[pane.id]:changed}}:{});};
  const setPaneContextPack = async (_id:string,dir:string)=> {
   const valid=captureSessionGesture(session);if(!valid())return;
   const changed=await api.setPaneContextPack(pane.id,dir,session.pane.cols,session.pane.rows,session.scope);if(valid())applyPaneSnapshot(changed);
  };
  const markActivity = useStore((s) => s.markActivity);
  const lastPrompts = useStore((s) => s.lastPrompts[key] ?? NO_PROMPTS);
  const registerSender = (_id: string, fn: Parameters<ReturnType<typeof useStore.getState>['registerSender']>[1]) => { registered.current['sender'] = fn; useStore.getState().registerSender(key,fn); };
  const unregisterSender = (_id: string) => useStore.getState().unregisterSender(key,registered.current['sender']);
  const registerPaneSnapshot = (_id: string, fn: Parameters<ReturnType<typeof useStore.getState>['registerPaneSnapshot']>[1]) => { registered.current['paneSnapshot'] = fn; useStore.getState().registerPaneSnapshot(key,fn); };
  const unregisterPaneSnapshot = (_id: string) => useStore.getState().unregisterPaneSnapshot(key,registered.current['paneSnapshot']);
  const registerClaimer = (_id: string, fn: Parameters<ReturnType<typeof useStore.getState>['registerClaimer']>[1]) => { registered.current['claimer'] = fn; useStore.getState().registerClaimer(key,fn); };
  const unregisterClaimer = (_id: string) => useStore.getState().unregisterClaimer(key,registered.current['claimer']);
  const registerRedrawer = (_id: string, fn: Parameters<ReturnType<typeof useStore.getState>['registerRedrawer']>[1]) => { registered.current['redrawer'] = fn; useStore.getState().registerRedrawer(key,fn); };
  const unregisterRedrawer = (_id: string) => useStore.getState().unregisterRedrawer(key,registered.current['redrawer']);
  const registerRealigner = (_id: string, fn: Parameters<ReturnType<typeof useStore.getState>['registerRealigner']>[1]) => { registered.current['realigner'] = fn; useStore.getState().registerRealigner(key,fn); };
  const unregisterRealigner = (_id: string) => useStore.getState().unregisterRealigner(key,registered.current['realigner']);
  const redrawPane = useStore((s) => s.redrawPane);
  const realignPane = useStore((s) => s.realignPane);
  const setPaneOwned = useStore((s) => s.setPaneOwned);
  const clearPaneOwnership = useStore((s) => s.clearPaneOwnership);
  const inputLocked = useStore((s) => s.paneOwnership[key] === false);
  // Truthful lock copy: 'none' means nobody owns the pane (daemon restart /
  // owner left) — a different message from a real peer takeover ('other').
  const inputLockUnowned = useStore((s) => s.paneOwnerState[key] === 'none');
  const launchClaudeHere = useStore((s) => s.launchClaudeHere);
  const launchShellHere = useStore((s) => s.launchShellHere);
  const movePane = useStore((s) => s.movePaneInLayout);
  const clientActivityMs = useStore((s) => s.clientActivityMs[pane.id] ?? 0);
  const lastViewedMs = useStore((s) => s.lastViewedMs[pane.id] ?? 0);
  const isZoomed = useStore((s) => s.zoomedPaneId === pane.id);
  // Subscribe to the stable `s.layout` ref (only re-minted on a real
  // structural layout change) and derive the count via useMemo. The old
  // `useStore((s) => collectPaneIds(s.layout).length)` re-ran the
  // recursive tree-walk on EVERY store update (per pane → O(N²) per tick);
  // now collectPaneIds runs only when the layout tree actually mutates.
  const layout = useStore((s) => s.layout);
  const paneCount = useMemo(() => collectPaneIds(layout).length, [layout]);
  const toggleZoom = useStore((s) => s.toggleZoom);
  const canZoom = paneCount > 1 || isZoomed;
  const [connStatus, setConnStatus] = useState<'connecting' | 'open' | 'reconnecting' | 'closed'>('connecting');
  const paneReaderMode = usePaneReaderMode({ paneId: key, termRef, actionGuard:canAct });
  // Brief "settling" veil shown on mobile pane mount. Hides the
  // visible transition where the ring-buffer replay renders first,
  // then Claude's SIGWINCH + Ctrl+L redraw overwrites it. Flipped
  // off after ~650ms — by then both refit passes + the second
  // Ctrl+L volley have fired and the alt-screen is stable.
  const [settling, setSettling] = useState(true);
  // Replay catch-up veil. 'active' = opaque cover while a large replay
  // parses; 'fading' = replay done, brief opacity transition; null = off.
  // Managed by the WS lifecycle below (begin on replay-start, end when
  // the replay flush completes or the socket closes).
  const [catchup, setCatchup] = useState<null | 'active' | 'fading'>(null);
  // Conversation-discontinuity banner (pane.switchNotice): a Focus→Terminal
  // switch that interrupted a turn, a restart-repaired resume, or a dropped
  // --resume (fresh start). Session-local dismissal keyed by notice.at — same
  // contract as NativePane's banner; the daemon clears the notice itself on
  // the next committed prompt.
  const [dismissedNotices, setDismissedNotices] = useState<Set<number>>(() => new Set());
  const paneSender = useStore((s) => s.senders[key]);
  // Renderer switch in flight (Focus→Terminal): drives the labeled scrim so
  // the fresh xterm's blank beat reads as an intentional transition.
  const modeSwitching = useStore((s) => !!s.paneModeSwitching[pane.id]);
  useEffect(() => {
    // 300ms covers the two refit passes (fitAddon runs at mount + 250ms)
    // plus xterm's internal layout flush. Previously 650ms, which added
    // dead time once redraws got fast enough to render well before the
    // veil lifted. See also the pane-settling-fade keyframes (styles.css).
    const h = window.setTimeout(() => setSettling(false), 300);
    return () => window.clearTimeout(h);
  }, [pane.id]);

  // When focus moves to this pane — via Ctrl+Shift+Arrow, Alt+H/J/K/L,
  // Alt+1..9, `[` / `]`, or any other keyboard path that flips the
  // store's focusedPaneId — re-route DOM focus to xterm's helper
  // textarea too. Without this, setFocus only updates the ring/badge;
  // keystrokes stay on whatever previously held activeElement
  // (usually the pane you just left), so typing lands in the wrong
  // terminal. Mouse clicks don't need this — onMouseDownCapture fires
  // alongside the native mousedown which natively focuses the textarea.
  useEffect(() => {
    // Spend the deliberate-selection marker UP-FRONT (one-shot in time) so a
    // later background re-run can't replay userPicked and bypass the typing
    // guard. Mirror of NativePane. (Audit 2026-06-26.)
    if (!canAct()) return;
    const userPicked = viewKind === 'workspace' && useStore.getState().lastUserFocusId === pane.id;
    if (userPicked) useStore.getState().consumeUserFocus();
    if (!focused) return;
    const t = termRef.current;
    if (!t) return;
    // Desktop only. On mobile, programmatically focusing xterm's hidden
    // (off-screen) helper textarea summons the soft keyboard AND makes the
    // browser pan the viewport to chase the textarea — typed text appears to
    // scroll up into history — and the focus bounce injects ESC[I/ESC[O into
    // the PTY (see the onData focus-report guard). Mobile users focus by
    // tapping the pane (native focus); we must not auto-steal focus on every
    // focusedPaneId change. Desktop keyboard-nav focus routing still needs it.
    if (isMobileViewport()) return;
    // Without a fresh deliberate selection, fall through to safe-by-default:
    // never steal from a field the user is actively typing in.
    if (!userPicked && isTypingElsewhere(t.textarea ?? null)) return;
    t.focus();
  }, [focused]);
  const [dropZone, setDropZone] = useState<DropZone | null>(null);
  const [beingDragged, setBeingDragged] = useState(false);
  const [editingTitle, setEditingTitle] = useState(false);
  const [contextPackDialogOpen, setContextPackDialogOpen] = useState(false);
  const [identityDialogOpen, setIdentityDialogOpen] = useState(false);

  const [lastPromptExpanded, setLastPromptExpanded] = useState(false);
  const paneFind = usePaneFind({ paneId: pane.id, searchAddonRef, termRef, actionGuard:canAct, captureGuard:()=>captureSessionGesture(session) });

  const [titleDraft, setTitleDraft] = useState('');
  // Flag-for-attention inline memo editor. Mirrors editingTitle/titleDraft.
  // The pane is flagged eagerly on the context-menu click (so the highlight
  // appears immediately); the memo input that drops in afterwards just edits
  // the existing memo. Cancelling the input leaves the flag in place — an
  // empty-memo flag is still a valid "come back to this" marker.
  const [editingFlagMemo, setEditingFlagMemo] = useState(false);
  const [flagMemoDraft, setFlagMemoDraft] = useState('');
  const {
    ctxMenu,
    ctxMenuRef,
    openContextMenu,
    closeContextMenu,
    actions: ctxMenuActions,
  } = usePaneContextMenu({
    pane,
    scope:session.scope, onPaneChanged:applyPaneSnapshot, actionGuard: actionValid, captureGuard:()=>captureSessionGesture(session), managedOwner:ownerPresentation,
    killPane,
    setFocus,
    setTitleDraft,
    setEditingTitle,
    setFlagMemoDraft,
    setEditingFlagMemo,
  });
  // Selection actions in the context menu: capture the terminal selection and
  // the other running panes at the moment the menu opens.
  const [menuSelection, setMenuSelection] = useState('');
  const [menuSendTargets, setMenuSendTargets] = useState<{ id: string; title: string; pid: number }[]>([]);
  useEffect(() => {
    if (!ctxMenu) {
      setMenuSelection('');
      return;
    }
    const sel = termRef.current?.getSelection() ?? '';
    setMenuSelection(sel);
    if (!sel) return;
    const st = useStore.getState();
    setMenuSendTargets(
      collectPaneIds(st.layout)
        .filter((id) => id !== pane.id)
        .map((id) => st.panes[id])
        .filter((p): p is PaneInfo => !!p && p.status === 'running' && p.kind !== 'native')
        .slice(0, 8)
        .map((p) => ({ id: p.id, title: p.title || p.cmd.join(' '), pid: p.pid })),
    );
  }, [ctxMenu, pane.id]);
  // "Send selection to <pane>" from another pane's menu lands here. It must
  // never run anything (lib/selectionSend.ts): it is bound to the pane
  // incarnation (pid) the user picked, and multi-line text is never typed —
  // it goes to the clipboard instead.
  // xterm's paste() then rides onData, so ownership gating is the same as typing.
  useEffect(() => {
    const onPaste = (e: Event) => {
      const d = (e as CustomEvent<{ paneId?: string; pid?: number; text?: string }>).detail;
      if (!d || d.paneId !== pane.id || !d.text || !canAct()) return;
      const st = useStore.getState();
      const live = session.pane;
      const term = termRef.current;
      if (!term || !live || live.status !== 'running' || live.pid !== d.pid) {
        st.toast('Not sent — that pane restarted since you opened the menu', { kind: 'warn', ttlMs: 4000 });
        return;
      }
      const plan = planSelectionSend(d.text);
      if (plan.action === 'paste') {
        term.paste(plan.text);
        return;
      }
      if (plan.reason === 'multiline-unsafe') {
        void copyToClipboard(plan.text);
        st.toast('Multi-line text is never typed into a pane (lines could run). Copied to the clipboard — paste it there yourself.', { kind: 'warn', ttlMs: 6000 });
      }
    };
    window.addEventListener('solu:pane-paste', onPaste);
    return () => window.removeEventListener('solu:pane-paste', onPaste);
  }, [pane.id]);
  // Ownership — daemon sends {type:"ownership", owned} text frames.
  // We push it into the central store (paneOwnership) so PaneGrid
  // can render a single session-level overlay. Local ref keeps a
  // synchronous view for the xterm onData input-gate.
  const ownedRef = useRef<boolean | null>(null);
  // xterm's answers to replayed queries are not typing: dropped while a
  // history replay (not an exact resume) parses (lib/terminalReplies.ts).
  const replayAnswersRef = useRef(new ReplayAnswerGate());
  const terminalThemeName = useStore((s) => s.terminalThemeName);
  const terminalThemeExplicit = useStore((s) => s.terminalThemeExplicit);
  const appThemeLight = useStore((s) => s.appThemeLight);
  // The pane surface (and its catch-up / settling veils) take the scheme's
  // background from the very first render, before xterm mounts and before
  // applyTerminalTheme runs in an effect, so a light pane never shows black.
  const terminalBackground = resolveTerminalTheme({
    terminalThemeName,
    terminalThemeExplicit,
    appThemeLight,
  }).xterm.background;
  const terminalFontSize = useStore((s) => s.terminalFontSize);
  const terminalLineHeight = useStore((s) => s.terminalLineHeight);
  const isMobileView = useIsMobileView();

  // Stable callback for CustomScrollbar. Must NOT be recreated on
  // every render — the scrollbar's effect depends on it, and a new
  // reference each render would re-run the effect, tear down and
  // reattach listeners, and queue retry timers that accumulate
  // across pane switches (visible as progressive flashing).
  const getXtermViewport = useCallback(
    () => hostRef.current?.querySelector('.xterm-viewport') as HTMLElement | null,
    [],
  );

  // Treat this as a Claude pane if Claude was the direct command OR is
  // running anywhere in the descendant process tree (server-reported
  // hasClaude). Drives the "⚡ Claude here" button visibility.
  const isClaudePane =
    pane.cmd[0] === 'claude' ||
    pane.cmd[0]?.endsWith('/claude') ||
    pane.hasClaude === true;
  const isCodexPane =
    pane.cmd[0] === 'codex' ||
    pane.cmd[0]?.endsWith('/codex') ||
    pane.hasCodex === true;
  const isMusePane =
    pane.cmd[0] === 'muse' ||
    pane.cmd[0]?.endsWith('/muse') ||
    pane.hasMuse === true;
  // Every terminal pane gets the reader chip. Claude/Codex/Muse were the
  // original gate, but managed harnesses (DeepSeek, ZCode) and plain shells
  // share the same xterm scrollback, and the chip only appears after the user
  // scrolls away — so there is no clutter cost and the "jump to latest"
  // affordance is now identical on every pane.
  const showsReaderChip = true;

  const effectiveActivity = Math.max(pane.lastActivityMs ?? 0, clientActivityMs);
  // What this pane has that you haven't seen (lib/turnChip.ts paneUnread):
  // a finished agent turn (the header chip's "new" tag) or plain output (the
  // dot). Spinner frames and agent redraws no longer count as news.
  const unreadKind = focused ? null : paneUnread(pane, lastViewedMs, effectiveActivity);
  const unread = unreadKind !== null;


  const [activityNow, setActivityNow] = useState(() => Date.now());
  useEffect(() => {
    // Only schedule a render when the short client-side "busy" window
    // needs to expire. This avoids one permanent timer per pane.
    if (!canAct() || !clientActivityMs) return;
    const delay = clientActivityMs + 1550 - Date.now();
    if (delay <= 0) {
      setActivityNow(Date.now());
      return;
    }
    const h = window.setTimeout(() => setActivityNow(Date.now()), delay);
    return () => window.clearTimeout(h);
  }, [clientActivityMs,viewKind,renderedGeneration]);

  // Prefer the server-computed state (busy / awaiting-input / choice-prompt /
  // recent / idle / exited). The client can also mark fresh activity it
  // witnesses over the WebSocket as "busy" before the next poll arrives.
  const activityClass = useMemo(() => {
    if (pane.status === 'exited') return 'exited';
    const freshByClient = activityNow - clientActivityMs < 1500;
    if (freshByClient) return 'busy';
    return pane.state || 'idle';
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [pane.state, pane.status, clientActivityMs, activityNow]);

  useEffect(() => {
    if (!hostRef.current) return;
    // Detect phone-width so we can (a) request a `force=1` WebSocket
    // subscription — tells the daemon to pick PTY size from OUR cols,
    // ignoring any desktop viewer that would otherwise keep the PTY
    // wide — and (b) fire a Ctrl+L after connect to redraw the TUI
    // over any replayed-wider content. Font stays at 13px everywhere
    // for legibility; the fix for wrapping is the PTY-size correction,
    // not shrinking text.
    const viewportWidth =
      (typeof window !== 'undefined' && window.visualViewport?.width) ||
      (typeof window !== 'undefined' ? window.innerWidth : 1024);
    const isPhoneWidth = viewportWidth < 800;
    const term = new Terminal({
      fontFamily: '"JetBrains Mono","SF Mono","Menlo","Consolas",monospace',
      // Seed from the store's current values so a freshly-mounted pane
      // picks up the user's persisted size/height without needing the
      // live-apply effect to fire. The effect still re-runs on changes.
      fontSize: useStore.getState().terminalFontSize,
      lineHeight: useStore.getState().terminalLineHeight,
      cursorBlink: true,
      allowProposedApi: true,
      // Let a terminal-resident program ask for the text-area size with CSI 18 t
      // without moving the caret. The DeepSeek harness client uses it to measure
      // the pane's real width; the old cursor-position probe (jump to the right
      // margin, read back) flashed the caret on every keystroke and turn tick.
      windowOptions: { getWinSizeChars: true },
      // Scale scrollback DOWN for large layouts. 20000 lines × N terminals
      // is a lot of memory when Benjamin runs ~40 panes; the focused/common
      // small-layout case stays at the generous 20000 so nothing changes
      // there. This trades scrollback HISTORY for memory in big grids — see
      // scrollbackForPaneCount() for the thresholds. Seeded from the current
      // paneCount; a layout effect below updates it live as the count
      // crosses a threshold.
      scrollback: pane.role === 'task_owner' ? 20000 : scrollbackForPaneCount(paneCount),
      convertEol: false,
      macOptionIsMeta: true,
      // Wheel scroll speed. xterm's default of 1 line/tick feels
      // sluggish on tall buffers; 3 was too aggressive (trackpads
      // in pixel-delta mode turned into overscroll). 2 is the
      // goldilocks: a mouse notch moves ~2 lines, a trackpad flick
      // scrolls naturally. fastScrollSensitivity applies while Alt
      // is held for those rare big jumps.
      scrollSensitivity: 2,
      fastScrollSensitivity: 10,
      // Programs paint their own colours, and a light background is where pale
      // ANSI foregrounds can become unreadable. xterm adjusts only offending
      // foregrounds; 4.5 targets AA for normal text without flattening syntax.
      // SGR 2 is intentionally exempt from that guarantee: xterm 5.5's
      // DomRendererRowFactory._applyMinimumContrast halves the requested ratio
      // for dim cells (2.25 here) so dim output remains visually distinct.
      minimumContrastRatio: 4.5,
    });
    applyTerminalTheme(term, hostRef.current, resolveTerminalTheme(useStore.getState()));
    // Tracks effect teardown for the async document.fonts.ready callback
    // — declared before the callback can fire, used again later by the
    // WebSocket lifecycle code.
    let disposed = false;

    // Live-terminal registry for diagnostics: scroll-stuck repros and the
    // Alt+Shift+D overlay need to read xterm viewport internals per pane
    // from the console / Playwright. Deleted in the dispose path below.
    const debugWin = window as unknown as { __soluTerms?: Map<string, Terminal> };
    (debugWin.__soluTerms ??= new Map()).set(key, term);

    const fit = new FitAddon();
    const weblinks = isEmbedded() ? new WebLinksAddon((_event, url) => { openEmbedUrl(url); }) : new WebLinksAddon();
    // Search addon powers "reveal match" from the cross-pane search in
    // CommandPalette. The addon runs against what xterm has in its own
    // scrollback (raw rendered text), not what the daemon returned, so
    // a match found by the daemon's stripped-text scan may not find a
    // corresponding xterm match — we treat findNext as best-effort.
    const searchAddon = new SearchAddon();
    searchAddonRef.current = searchAddon;
    const findResultsDisp = searchAddon.onDidChangeResults(paneFind.handleResults);
    term.loadAddon(fit);
    term.loadAddon(weblinks);
    term.loadAddon(searchAddon);

    // OSC 52 — terminal-resident programs (Claude Code's `/copy`, vim,
    // tmux, etc.) ask the emulator to write to the system clipboard
    // by emitting `ESC ] 52 ; c ; <base64> BEL`. xterm.js doesn't wire
    // this to navigator.clipboard by default, so without this handler
    // `/copy` was a no-op inside soluterminal panes.
    const oscCopyDisp = term.parser.registerOscHandler(52, (data) => {
      if(!canAct() || ownedRef.current !== true)return true;
      const semi = data.indexOf(';');
      if (semi < 0) return false;
      const payload = data.slice(semi + 1);
      // "?" is a paste-request asking the terminal to send the
      // clipboard back to the program — refuse, exfiltration risk.
      if (payload === '?') return true;
      try {
        // OSC 52 carries `base64(utf8_bytes(text))`. `atob` returns a
        // "binary string" — one JS code unit per decoded byte — so
        // multibyte UTF-8 sequences must be reassembled and decoded
        // explicitly. Passing the binary string straight to
        // `writeText` would write each UTF-8 byte as its own UCS-2
        // code point, mangling em-dashes, CJK, emoji, etc. into
        // Latin-1 mojibake (e.g. `—` → `â\x80\x94`).
        const bin = atob(payload);
        const bytes = new Uint8Array(bin.length);
        for (let i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
        const text = new TextDecoder('utf-8').decode(bytes);
        void navigator.clipboard?.writeText?.(text).catch(() => {});
      } catch { /* malformed base64 — drop */ }
      return true;
    });

    // OSC 7658 — the terminal client reports a PTY/xterm width disagreement
    // (`SoluWidth=<pty>;<measured>`, re-asserted through the reconnect self-heal)
    // and its count of running work (`SoluWork=<n>`, read by the × close dialog
    // so it can warn before killing an in-flight turn or background job).
    const oscSoluDisp = term.parser.registerOscHandler(7658, (data) => {
      const width = /^SoluWidth=(\d+);(\d+)$/.exec(data);
      if (width) {
        const pty = Number(width[1]);
        const measured = Number(width[2]);
        if (pty > 0 && measured > 0 && pty !== measured && term.cols === measured) {
          realign('pty-width-mismatch');
        }
        return true;
      }
      const work = /^SoluWork=(\d+)$/.exec(data);
      if (work) {
        setPaneRunningWork(key, Number(work[1]));
        return true;
      }
      return false;
    });

    term.open(hostRef.current);
    // xterm 5.5 queues an uncancelled initial viewport sync. A fast workspace
    // change (or StrictMode cleanup) may dispose its renderer before it runs.
    const viewport = (term as unknown as { _core?: { viewport?: { syncScrollArea: (immediate?: boolean) => void } } })._core?.viewport;
    if (viewport) {
      const syncScrollArea = viewport.syncScrollArea.bind(viewport);
      viewport.syncScrollArea = (immediate) => { if (!disposed) syncScrollArea(immediate); };
    }

    // Click-to-open file paths in terminal output. Claude (and many
    // CLIs) print paths like `/home/x/foo.md`, `~/notes.txt`,
    // `./web/src/Pane.tsx`, often with a `:line:col` suffix. We
    // detect those and route a click to openFileHere — same code
    // path as the sidebar's Files input — instead of forcing the
    // user to copy/paste. URLs stay on WebLinksAddon (external).
    //
    // Only "/", "~/", "./", "../" prefixes — bare-relative shapes
    // like `package.json` are too prone to false positives in
    // prose. The negative-precedence char class on the leading
    // group keeps us out of `https://...` and similar.
    const PATH_RE = /(?:^|[\s"'`(\[<>])((?:~|\.{1,2})?\/[A-Za-z0-9_./@\-+]+(?::\d+(?::\d+)?)?)/g;
    const linkProviderDisp = term.registerLinkProvider({
      provideLinks(bufferLineNumber, callback) {
        const line = term.buffer.active.getLine(bufferLineNumber - 1);
        if (!line) { callback(undefined); return; }
        const text = line.translateToString(true);
        if (!text) { callback(undefined); return; }
        const links: Array<{
          range: { start: { x: number; y: number }; end: { x: number; y: number } };
          text: string;
          activate: (event: MouseEvent, text: string) => void;
        }> = [];
        PATH_RE.lastIndex = 0;
        let m: RegExpExecArray | null;
        while ((m = PATH_RE.exec(text)) !== null) {
          const captureStart = m.index + (m[0].length - m[1].length);
          // Trim trailing punctuation (commas, parens, quotes) but
          // keep :N:M numeric suffixes.
          const trimmed = m[1].replace(/[.,;)\]>"'`]+$/, '');
          if (!trimmed) continue;
          links.push({
            range: {
              start: { x: captureStart + 1, y: bufferLineNumber },
              end: { x: captureStart + trimmed.length, y: bufferLineNumber },
            },
            text: trimmed,
            activate: (event, linkText) => {
              if(!canAct())return;
              event.preventDefault();
              openTerminalFileLink(linkText, resolvePathForOpen, (path) => {
                useStore.getState().openFileHere(path);
              });
            },
          });
        }
        callback(links.length ? links : undefined);
      },
    });

    // Resolve relative paths against the focused pane's live cwd
    // (snapshot at click time, not effect-mount time, so cd'ing
    // inside the pane is reflected). Absolute / home-relative
    // paths pass through — the daemon canonicalizes ~.
    function resolvePathForOpen(p: string): string | null {
      const t = p.trim();
      if (!t) return null;
      if (t.startsWith('/') || t.startsWith('~')) return t;
      const latest = session.pane;
      const base = latest?.liveCwd || latest?.cwd;
      if (!base) return t;
      const rel = t.startsWith('./') ? t.slice(2) : t;
      return base.endsWith('/') ? base + rel : `${base}/${rel}`;
    }

    // Mobile: bypass xterm's JS-driven touch scroll.
    //
    // xterm registers a passive:false touchmove listener on .xterm
    // (Terminal.ts:841) that, on every frame of finger movement, reads the
    // delta, writes .xterm-viewport.scrollTop += deltaY, and preventDefault's
    // the gesture so no native scroll happens. On desktop this is fine. On
    // mobile it saturates the main thread during the initial touchmove burst,
    // producing the "touch-and-immediately-drag is laggy, touch-hold-then-drag
    // is smooth" pattern Benjamin reported — the held start gives the browser
    // a chance to settle its own gesture classifier before events start
    // firing; the immediate drag has no such grace period.
    //
    // .xterm-viewport already has overflow-y:scroll and sits at absolute
    // 0,0,0,0 under .xterm-screen (siblings, Terminal.ts:426-442). Two
    // changes let the browser's compositor handle scroll natively:
    //   1. .xterm-screen → pointer-events:none: touches fall through to the
    //      viewport underneath.
    //   2. Stop touch events on the viewport from bubbling to .xterm, where
    //      xterm's passive:false handler would fire and preventDefault.
    // xterm's own scroll listener on the viewport (Viewport.ts:71) still runs
    // on native scroll, so ydisp and rendered rows stay in sync.
    //
    // Tradeoff: xterm's touch-to-mouse translation for TUI apps with mouse
    // support is disabled on phone width. Claude Code doesn't use mouse, and
    // the scroll smoothness is the priority on mobile.
    let teardownMobileTouchFix: (() => void) | null = null;
    if (isPhoneWidth && hostRef.current) {
      const xtermScreen = hostRef.current.querySelector('.xterm-screen') as HTMLElement | null;
      const xtermViewport = hostRef.current.querySelector('.xterm-viewport') as HTMLElement | null;
      if (xtermScreen && xtermViewport) {
        xtermScreen.style.pointerEvents = 'none';
        const stop = (e: Event) => e.stopPropagation();
        xtermViewport.addEventListener('touchstart', stop, { passive: true });
        xtermViewport.addEventListener('touchmove', stop, { passive: true });
        xtermViewport.addEventListener('touchend', stop, { passive: true });
        xtermViewport.addEventListener('touchcancel', stop, { passive: true });
        teardownMobileTouchFix = () => {
          xtermScreen.style.pointerEvents = '';
          xtermViewport.removeEventListener('touchstart', stop);
          xtermViewport.removeEventListener('touchmove', stop);
          xtermViewport.removeEventListener('touchend', stop);
          xtermViewport.removeEventListener('touchcancel', stop);
        };
      }
    }

    // Preserve scroll position across pane resize. Works from anywhere
    // in the buffer, stable across many interleaved resize events.
    //
    // Root cause (direct read of xterm.js Viewport source):
    //   1. Viewport._innerRefresh is rAF-debounced and re-sets
    //        scrollTop = ydisp × rowHeight
    //      whenever the container height changes. A synchronous restore
    //      after fit.fit() gets OVERWRITTEN by that rAF next frame — and
    //      whether it wins the race is scheduler-dependent, which is
    //      exactly the intermittency the user reported.
    //   2. xterm computes _currentRowHeight from the render service's
    //      cell dimensions, which CAN shift by fractional pixels when the
    //      canvas resizes. That shifts the ydisp ↔ scrollTop mapping, so
    //      "same pixel scrollTop" doesn't always mean "same line".
    //
    // Defensive fix (belt and suspenders — each layer is necessary for
    // one of the two failure modes):
    //
    //   A. Capture the PRE-drag viewportY AND scrollTop on pointerdown of
    //      the resize handle — before any layout mutation, so the snapshot
    //      isn't already corrupted by xterm's internal reaction.
    //   B. After fit.fit(), run our restore inside a DOUBLE-rAF so it
    //      lands AFTER xterm's own rAF-debounced refresh has settled.
    //   C. Restore using xterm's scrollToLine()/scrollToBottom() API —
    //      line-indexed, so rowHeight fluctuation doesn't affect the
    //      target line. Follow with a direct scrollTop write as a second
    //      anchor in case the API call gets re-synced.
    // NEAR_BOTTOM_FOLLOW_LINES: when the pre-drag position was within this
    // many lines of the buffer bottom, the restore anchors to
    // linesFromBottom (thumb stays visually put, content follows new
    // writes). Beyond this threshold we lock to the absolute viewportY
    // (user is reading history; don't yank them down).
    //
    // The user's diag trace showed that even when they weren't at the
    // strict bottom — e.g. 4 lines above it — a small burst of writes
    // during the drag pushed them from "4 lines from bottom" to "13 lines
    // from bottom" because we locked to absolute ydisp. The scrollbar
    // thumb visibly moved as a result. Near-bottom readers want the
    // thumb stable; history readers want content stable. 10-line threshold
    // covers the "following live output" case without yanking anyone
    // who's genuinely scrolled up.
    const NEAR_BOTTOM_FOLLOW_LINES = 10;
    const preDragRef = { current: {
      viewportY: 0,
      scrollTop: 0,
      linesFromBottom: 0,
      rows: 0,
      cols: 0,
      rectTop: 0,
      rectBottom: 0,
      wasAtBottom: true,
      followFromBottom: false,
    } };
    const draggingRef = { current: false };
    let restoreSeq = 0;
    let pendingRestoreSeq = 0;

    // A user scroll is NEWER intent than any in-flight resize restore.
    // fitPreservingScroll snapshots the position, fits, then restores in
    // a double-rAF — and while that restore is pending, wheel snapshots
    // are skipped, so the snapshot goes stale. Under continuous resize
    // churn (last-prompt strip growing while Claude streams, header
    // wrapping, approval banners) the restores land back-to-back and
    // each one re-applied the stale position, yanking the viewport back
    // and erasing every tick of the user's downward scroll — the
    // "can't scroll back down, stuck until Jump-to-live" bug (verified
    // by Playwright repro: wheel-down + 8px height oscillation pinned
    // the viewport 386 lines above bottom indefinitely). Bumping
    // restoreSeq makes the pending double-rAF callback no-op (it
    // re-checks the token); zeroing pendingRestoreSeq lets the wheel's
    // deferred snapshot run so the NEXT fit preserves the position the
    // user actually scrolled to.
    const cancelPendingRestore = () => {
      if (pendingRestoreSeq === 0) return;
      restoreSeq++;
      pendingRestoreSeq = 0;
    };

    // User scroll also RE-BASELINES the restore anchor, bypassing the
    // draggingRef guard. The ResizeObserver below holds draggingRef true
    // for the whole resize burst (200ms-renewed), freezing preDragRef at
    // the burst-start position so splitter drags don't drift. But UI
    // chrome churn (last-prompt strip, banners) produces the same RO
    // cadence as a drag, and with the baseline frozen, every restore
    // reverted any wheel scrolling done during the burst — the user was
    // locked to the burst-start line until the churn stopped (the
    // stuck-scroll root cause; see the 2026-06-12 diag traces). A scroll
    // is explicit user intent: wherever they scrolled to IS the new
    // baseline, drag or no drag. Double-rAF so the capture lands after
    // the scroll steps have applied the wheel to the buffer.
    let rebaselineRafOuter = 0;
    let rebaselineRafInner = 0;
    const rebaselineAfterUserScroll = () => {
      cancelPendingRestore();
      if (rebaselineRafOuter || rebaselineRafInner) return;
      rebaselineRafOuter = requestAnimationFrame(() => {
        rebaselineRafOuter = 0;
        rebaselineRafInner = requestAnimationFrame(() => {
          rebaselineRafInner = 0;
          snapshot();
        });
      });
    };

    const readViewport = (): HTMLElement | null =>
      (term.element?.querySelector('.xterm-viewport') as HTMLElement | null) ?? null;

    // xterm 5.5's core exposes these as UNDERSCORE-prefixed privates
    // (_bufferService, _renderService) — `viewport` alone is bare. This
    // helper originally read `bufferService`/`renderService` (no
    // underscore), which are undefined on the real object, so every
    // restore silently took the raw-scrollTop legacy fallback and the
    // whole line-indexed restore path NEVER ran — the proven root cause
    // of the stuck-scrollback bug (a stale snapshot's pixel scrollTop
    // got re-applied after each resize, erasing the user's wheel
    // progress; see the 2026-06-12 ydisp/scrollTop write-trap trace).
    // Resolve underscore-first with bare-name fallback so an xterm
    // upgrade that de-privatizes the fields keeps working.
    interface XtermCoreShape {
      _bufferService?: XtermBufferService;
      bufferService?: XtermBufferService;
      viewport?: { _ignoreNextScrollEvent: boolean; _innerRefresh?: () => void; _currentRowHeight?: number };
      _renderService?: XtermRenderService;
      renderService?: XtermRenderService;
    }
    interface XtermBufferService {
      buffer?: { ydisp: number; ybase: number; lines?: { length: number } };
      isUserScrolling?: boolean;
    }
    interface XtermRenderService {
      dimensions?: { css?: { cell?: { height: number } } };
    }
    const withXtermCore = () => {
      const core = (term as unknown as { _core?: XtermCoreShape })._core;
      if (!core) return undefined;
      return {
        bufferService: core._bufferService ?? core.bufferService,
        viewport: core.viewport,
        renderService: core._renderService ?? core.renderService,
      };
    };

    const snapshot = () => {
      const buf = term.buffer.active;
      const vp = readViewport();
      const hostEl = hostRef.current;
      const rect = hostEl?.getBoundingClientRect();
      const linesFromBottom = Math.max(0, buf.length - (buf.viewportY + term.rows));
      const wasAtBottom = linesFromBottom === 0;
      preDragRef.current = {
        viewportY: buf.viewportY,
        scrollTop: vp?.scrollTop ?? 0,
        linesFromBottom,
        rows: term.rows,
        cols: term.cols,
        // Pane container screen rect at snapshot time. We use this in the
        // fit wrapper to detect TOP-anchored vs BOTTOM-anchored resize:
        // if rect.top moved and rect.bottom stayed, the pane is below a
        // resize handle (bottom pane of a stack — its top edge is what's
        // moving during the drag, bottom is pinned). That matters because
        // xterm paints rows top-down from the container's top, so a
        // bottom-anchored pane that doesn't adjust ydisp has its entire
        // visible content jerk on screen as the container top moves.
        rectTop: rect?.top ?? 0,
        rectBottom: rect?.bottom ?? 0,
        wasAtBottom,
        // Follow-from-bottom means we preserve distance-from-end instead
        // of absolute line. For users within NEAR_BOTTOM_FOLLOW_LINES of
        // the end this keeps the scrollbar visually locked even as writes
        // grow the buffer mid-drag.
        followFromBottom: linesFromBottom > 0 && linesFromBottom <= NEAR_BOTTOM_FOLLOW_LINES,
      };
    };

    const resumeFollowIfNearBottom = () => {
      const core = withXtermCore();
      const buffer = core?.bufferService?.buffer;
      const vpEl = readViewport();
      if (!buffer || !core?.bufferService) return;
      const currentLen = buffer.lines?.length ?? term.buffer.active.length;
      const maxY = Math.max(0, currentLen - term.rows);
      const linesFromBottom = Math.max(0, currentLen - (buffer.ydisp + term.rows));
      if (linesFromBottom > NEAR_BOTTOM_FOLLOW_LINES) return;
      buffer.ydisp = maxY;
      core.bufferService.isUserScrolling = false;
      if (vpEl) {
        const rowHeight = core.renderService?.dimensions?.css?.cell?.height ?? 0;
        const desired = rowHeight > 0 ? maxY * rowHeight : vpEl.scrollHeight;
        // Clamp to what the DOM can actually reach, and arm
        // _ignoreNextScrollEvent only when the write will move scrollTop.
        // Arming before a no-op write leaves the flag set, and xterm then
        // swallows the user's NEXT real scroll event.
        const target = Math.min(desired, Math.max(0, vpEl.scrollHeight - vpEl.clientHeight));
        if (Math.abs(vpEl.scrollTop - target) >= 1) {
          if (core.viewport) core.viewport._ignoreNextScrollEvent = true;
          vpEl.scrollTop = target;
        }
      }
      snapshot();
    };

    const onGlobalPointerDown = (e: PointerEvent) => {
      if(!canAct())return;
      const target = e.target;
      if (!(target instanceof Element)) return;
      // Match a broader set of resize-handle markers. react-resizable-panels
      // variants / the library's internal wrapper div sometimes expose
      // different attributes; be forgiving so we don't miss the drag start
      // and fall back to in-wrapper snapshot (which captures post-drift).
      const handle =
        target.closest('[data-panel-resize-handle-id]') ||
        target.closest('[data-panel-resize-handle-active]') ||
        target.closest('[data-resize-handle]') ||
        target.closest('.sidebar-resize-handle') ||
        target.closest('.sidebar-section-resize');
      // Log EVERY pointerdown so we can see what the user actually clicked
      // when the handle selector misses — surfaces the real resize-handle
      // DOM shape in a field we can read from the overlay.
      const tCls = target.className && typeof target.className === 'string'
        ? '.' + target.className.split(' ').slice(0, 2).join('.')
        : '';
      logScrollDiag({
        t: performance.now(),
        paneId: pane.id,
        label: handle ? 'pointerdown-handle' : 'pointerdown-other',
        note: `<${target.tagName.toLowerCase()}${tCls}> type=${e.type}`,
      });
      if (handle) {
        snapshot();
        draggingRef.current = true;
        const s = preDragRef.current;
        logScrollDiag({
          t: performance.now(),
          paneId: pane.id,
          label: 'drag-start',
          saved: { viewportY: s.viewportY, scrollTop: s.scrollTop, wasAtBottom: s.wasAtBottom },
        });
      }
    };
    const onGlobalPointerUp = () => { draggingRef.current = false; };
    // mousedown capture as a fallback for any platform/browser path that
    // doesn't emit pointerdown (older touch shims, some accessibility tools).


    // Keep preDragRef fresh during non-drag time so the next drag starts
    // with an accurate snapshot. Everything here checks draggingRef first
    // to avoid capturing drifted mid-drag state.
    //
    //   - term.onWriteParsed: follows Claude's writes (ydisp auto-follow
    //     or eviction compensation happens inside xterm; our snapshot
    //     tracks whatever the user ends up seeing).
    //   - wheel / keydown on the host: follows user-driven scrolls.
    //
    // The rAF defer on wheel/keydown lets xterm's onScroll apply before
    // we read buffer.viewportY — otherwise we'd snapshot the pre-scroll
    // position.
    const maybeSnapshotIfIdle = () => {
      if (!canAct() || draggingRef.current) return;
      if (pendingRestoreSeq !== 0) return;
      snapshot();
    };
    let writeParsedSnapshotRaf = 0;
    let writeParsedSnapshotInnerRaf = 0;
    const scheduleWriteParsedSnapshot = () => {
      if (!canAct() || writeParsedSnapshotRaf || writeParsedSnapshotInnerRaf) return;
      // xterm applies viewport/scrollbar follow-up work around parser writes.
      // Snapshotting synchronously can catch the buffer after it grew but
      // before the viewport has followed, recording a false "user is reading
      // history" position. That stale snapshot is what later UI resizes
      // restore to, appearing as an upward jump after approvals/messages.
      writeParsedSnapshotRaf = requestAnimationFrame(() => {
        writeParsedSnapshotRaf = 0;
        writeParsedSnapshotInnerRaf = requestAnimationFrame(() => {
          writeParsedSnapshotInnerRaf = 0;
          maybeSnapshotIfIdle();
        });
      });
    };
    const writeParsedSnapshotDisp = term.onWriteParsed(scheduleWriteParsedSnapshot);
    const hostElForSnapshot = hostRef.current;
    const deferredMaybeSnapshot = () => requestAnimationFrame(maybeSnapshotIfIdle);

    // Pointer interaction inside the pane (Jump-to-live chip, mobile
    // scrollbar drag, selection) also outranks a pending restore. The
    // splitter resize handles live OUTSIDE the pane host, so drag-resize
    // snapshotting is unaffected.
    const cancelRestoreOnPointer = () => {if(canAct())rebaselineAfterUserScroll();};
    let inputHandlersAttached=false;
    const attachInputHandlers=()=>{
      if(inputHandlersAttached || !canAct())return;inputHandlersAttached=true;
      document.addEventListener('pointerdown',onGlobalPointerDown,true);
      document.addEventListener('mousedown',onGlobalPointerDown as EventListener,true);
      document.addEventListener('pointerup',onGlobalPointerUp,true);
      document.addEventListener('mouseup',onGlobalPointerUp,true);
      document.addEventListener('pointercancel',onGlobalPointerUp,true);
      hostElForSnapshot?.addEventListener('wheel',deferredMaybeSnapshot,{passive:true});
      hostElForSnapshot?.addEventListener('keydown',deferredMaybeSnapshot);
      hostElForSnapshot?.addEventListener('pointerdown',cancelRestoreOnPointer,true);
    };
    const detachInputHandlers=()=>{
      if(!inputHandlersAttached)return;inputHandlersAttached=false;
      document.removeEventListener('pointerdown',onGlobalPointerDown,true);
      document.removeEventListener('mousedown',onGlobalPointerDown as EventListener,true);
      document.removeEventListener('pointerup',onGlobalPointerUp,true);
      document.removeEventListener('mouseup',onGlobalPointerUp,true);
      document.removeEventListener('pointercancel',onGlobalPointerUp,true);
      hostElForSnapshot?.removeEventListener('wheel',deferredMaybeSnapshot);
      hostElForSnapshot?.removeEventListener('keydown',deferredMaybeSnapshot);
      hostElForSnapshot?.removeEventListener('pointerdown',cancelRestoreOnPointer,true);
    };
    attachInputHandlers();

    let lastGoodFit = { cols: term.cols, rows: term.rows };

    // Per-pane on-screen state for SIZING visibility. The daemon's
    // desiredSizeLocked only lets VISIBLE subs drive the shared PTY width; we
    // used to report whole-tab document.visibilityState, so a pane parked in a
    // background workspace/window kept voting with its (narrow) width and pinned
    // an actively-viewed pane narrow. Now visibility = tab-visible AND this
    // pane's host is on-screen (adopted by a slot, not parked). Seeded from the
    // host's current parked state; flipped by the park/reattach events below.
    let onScreen = !isPaneHostParked(key);
    const currentVisible = () =>
      (typeof document === 'undefined' || document.visibilityState === 'visible') && onScreen && canAct();
    const sendVisibilityNow = () => {
      const ws = wsRef.current;
      if (ws && ws.readyState === WebSocket.OPEN) {
        ws.send(JSON.stringify({ type: 'visibility', visible: currentVisible() }));
      }
    };
    // Re-stamp this view as the actively-viewed device for SIZING (wins
    // desiredSizeLocked) without changing input ownership — fired when this
    // pane is the focused, on-screen pane and its window regains focus, so the
    // pane the user is actually looking at reclaims the PTY width from a
    // background-tile or stale sub.
    const sendActiveSizing = () => {
      const ws = wsRef.current;
      if (ws && ws.readyState === WebSocket.OPEN && currentVisible()) {
        ws.send(JSON.stringify({ type: 'active' }));
      }
    };

    const readUsableHostRect = (source: string): DOMRect | null => {
      const host = hostRef.current;
      if (!host) return null;
      const rect = host.getBoundingClientRect();
      const visible = typeof document === 'undefined' || document.visibilityState === 'visible';
      // WebView2 can report transient tiny-but-nonzero rects while a
      // minimized desktop window is restoring. Fitting xterm against
      // that shape commits tiny cols and sends a bad PTY resize. Treat
      // those measurements like "not ready yet" and let the restore
      // refit scheduler try again after layout settles.
      const usable = visible && onScreen && host.isConnected && rect.width >= 80 && rect.height >= 80;
      if (!usable) {
        lifecycleLog('pane.fit.skip-unusable-rect', {
          paneId: pane.id,
          source,
          width: rect.width,
          height: rect.height,
          visibility: typeof document === 'undefined' ? 'unknown' : document.visibilityState,
          focused: typeof document !== 'undefined' && typeof document.hasFocus === 'function'
            ? document.hasFocus()
            : null,
        });
        return null;
      }
      return rect;
    };

    // Replay size pin. The daemon lines its reattach repaint up with the
    // terminal size this client announced at connect (term_cols/term_rows).
    // If the layout shifts before the replay is written (a notice or banner
    // appearing), the repaint would land on the wrong rows: duplicated lines
    // and an overwritten prompt. So the replay is written at the announced
    // size, and fitting waits until it has been parsed.
    let replayPin: { cols: number; rows: number } | null = null;
    const fitPreservingScroll = () => {
      if (replayPin) return false;
      if (!readUsableHostRect('fit-preserving-scroll')) return false;
      // While a splitter drag is in progress (draggingRef.current true),
      // reuse the pointerdown-anchored snapshot — mid-drag layout drift
      // would corrupt the baseline and each restore would compound the
      // error. For every OTHER fit (ResizeObserver churn from the
      // last-prompt strip / header, window resizes, refit timers), the
      // LIVE viewport is the source of truth: re-snapshot it here, now.
      // We previously trusted event-deferred snapshot maintenance
      // (wheel/keydown rAFs + onWriteParsed) to keep preDragRef fresh,
      // and it provably falls behind under churn — the diag trace shows
      // fits reading a stale snapshot while buf.viewportY already held
      // the user's newer position, so each restore yanked the user back:
      // THE stuck-scrollback root cause (2026-06-12).
      if (!draggingRef.current) snapshot();
      const saved = preDragRef.current;
      const bufPre = term.buffer.active;
      const vpPre = readViewport();
      logScrollDiag({
        t: performance.now(),
        paneId: pane.id,
        label: 'fit-pre',
        ydisp: bufPre.viewportY, length: bufPre.length, rows: term.rows, cols: term.cols,
        scrollTop: vpPre?.scrollTop, scrollHeight: vpPre?.scrollHeight, clientHeight: vpPre?.clientHeight,
        saved: { viewportY: saved.viewportY, scrollTop: saved.scrollTop, wasAtBottom: saved.wasAtBottom },
      });

      const restoreToken = ++restoreSeq;
      pendingRestoreSeq = restoreToken;
      fit.fit();
      // Floor cols to a Claude-legible width (see MIN_PANE_COLS). No-op
      // unless the pane measured narrower than the floor.
      if (term.cols > 0 && term.cols < MIN_PANE_COLS) {
        term.resize(MIN_PANE_COLS, term.rows);
      }
      if (term.cols > 0 && term.rows > 0) {
        lastGoodFit = { cols: term.cols, rows: term.rows };
      }
      // Post-fit position baseline. If the viewport moves between here
      // and the deferred restore two frames later, that movement is
      // newer intent (user wheel, keyboard nav, or xterm auto-follow) —
      // the restore must yield rather than yank the viewport back.
      const ydispAtFit = term.buffer.active.viewportY;

      const bufPost = term.buffer.active;
      const vpPost = readViewport();
      logScrollDiag({
        t: performance.now(),
        paneId: pane.id,
        label: 'fit-post',
        ydisp: bufPost.viewportY, length: bufPost.length, rows: term.rows, cols: term.cols,
        scrollTop: vpPost?.scrollTop, scrollHeight: vpPost?.scrollHeight, clientHeight: vpPost?.clientHeight,
      });

      requestAnimationFrame(() => {
        requestAnimationFrame(() => {
          if (disposed || restoreToken !== restoreSeq) return;
          if (term.buffer.active.viewportY !== ydispAtFit) {
            // Viewport moved since the fit — abort the restore and
            // re-snapshot so the NEXT fit preserves where the user
            // actually is, not where they were before this resize.
            if (pendingRestoreSeq === restoreToken) {
              pendingRestoreSeq = 0;
              snapshot();
            }
            logScrollDiag({
              t: performance.now(),
              paneId: pane.id,
              label: 'restore-abort-user-scroll',
              ydisp: term.buffer.active.viewportY,
              length: term.buffer.active.length,
              rows: term.rows,
              note: `ydispAtFit=${ydispAtFit}`,
            });
            return;
          }
          // Direct ydisp write via xterm's private bufferService. Diagnostic
          // capture confirmed term.scrollToLine(X) does NOT land on X: xterm
          // internally writes scrollTop = X × rowHeight, then its DOM
          // onScroll handler reads scrollTop back and derives
          //     ydisp = floor(scrollTop / currentRowHeight)
          // where currentRowHeight has shifted by fractional pixels across
          // the resize. The rounding loses 1-2 lines. scrollToLine is not
          // truly line-indexed — it's scrollTop-indexed-then-rounded-back.
          //
          // Bypass the DOM round-trip entirely: set ydisp directly, set
          // _ignoreNextScrollEvent so xterm's onScroll won't overwrite our
          // value, then pin scrollTop to match.
          const core = withXtermCore();
          const buffer = core?.bufferService?.buffer;
          const vpEl = readViewport();
          const rowHeight = core?.renderService?.dimensions?.css?.cell?.height ?? 0;

          const hostElNow = hostRef.current;
          const rectNow = hostElNow?.getBoundingClientRect();

          if (buffer && core?.viewport) {
            const currentLen = buffer.lines?.length ?? 0;

            // Four restore modes:
            //   wasAtBottom         → lock to bottom (auto-follow new writes)
            //   followFromBottom    → preserve linesFromBottom (scrollbar thumb
            //                         stays visually stable when writes grow
            //                         the buffer mid-drag; used for near-bottom
            //                         readers who were following live output)
            //   absolute (top pane) → keep saved.viewportY (top row stays on
            //                         same screen y because container top
            //                         didn't move)
            //   absolute (bot pane) → keep saved.viewportY - rowsDelta, so the
            //                         previously-visible content stays at the
            //                         same screen y even though the container
            //                         top moved (xterm paints top-down from
            //                         container; shift ydisp opposite to rows
            //                         delta and the pixel-level content
            //                         stays put).
            //   absolute + cols changed → trust xterm's own reflow; writing
            //                         saved.viewportY would land on
            //                         pre-reflow content that no longer
            //                         exists at that index.
            const restoreTarget = computePaneRestoreTarget(saved, {
              ydisp: buffer.ydisp,
              length: currentLen,
              rows: term.rows,
              cols: term.cols,
              rectTop: rectNow?.top,
              rectBottom: rectNow?.bottom,
            });
            const { targetY, skipYdisp } = restoreTarget;
            if (!skipYdisp) buffer.ydisp = targetY;

            // Reconcile the isUserScrolling flag with our target.
            // xterm gates auto-follow on writes to `!isUserScrolling`; our
            // direct ydisp write doesn't touch that flag, and a prior DOM
            // scroll may have left it stuck `true`, so without this, new
            // writes don't auto-follow even when we've restored to bottom.
            //   wasAtBottom → false  (resume auto-follow on subsequent writes)
            //   otherwise   → true   (keep xterm from yanking the viewer down)
            if (core.bufferService) {
              core.bufferService.isUserScrolling = restoreTarget.isUserScrolling;
            }

            // Re-sync viewport geometry through xterm's own refresh before
            // pinning. After a fit the scroll-area height and rowHeight are
            // stale until xterm's rAF-debounced refresh runs; pinning
            // scrollTop against stale geometry clamps at the OLD max while
            // ydisp points past it. In that state wheel-down produces no DOM
            // scroll events at all (scrollTop can't grow), so the pane reads
            // as "stuck above bottom until Jump-to-live". _innerRefresh
            // recomputes the scroll-area height and pins
            // scrollTop = ydisp × rowHeight itself with fresh numbers.
            core.viewport._innerRefresh?.();
            if (!skipYdisp && vpEl && rowHeight > 0) {
              // Fallback pin for builds where _innerRefresh is unavailable.
              // Clamp to the reachable range and arm _ignoreNextScrollEvent
              // only when the write will actually move scrollTop — arming
              // before a no-op write leaves the flag set and xterm swallows
              // the user's next real scroll event.
              const target = Math.min(
                targetY * rowHeight,
                Math.max(0, vpEl.scrollHeight - vpEl.clientHeight),
              );
              if (Math.abs(vpEl.scrollTop - target) >= 1) {
                core.viewport._ignoreNextScrollEvent = true;
                vpEl.scrollTop = target;
              }
            }
          } else if (vpEl) {
            // Fallback path if private API shape ever changes — at least
            // write DOM scrollTop, even if it's slightly lossy.
            if (saved.wasAtBottom) vpEl.scrollTop = vpEl.scrollHeight;
            else vpEl.scrollTop = saved.scrollTop;
          }

          const bufFin = term.buffer.active;
          const vpFin = readViewport();
          const mode = computePaneRestoreTarget(saved, {
            ydisp: term.buffer.active.viewportY,
            length: term.buffer.active.length,
            rows: term.rows,
            cols: term.cols,
            rectTop: rectNow?.top,
            rectBottom: rectNow?.bottom,
          }).mode;
          logScrollDiag({
            t: performance.now(),
            paneId: pane.id,
            label: saved.wasAtBottom ? 'restore-bottom' : 'restore-line',
            ydisp: bufFin.viewportY, length: bufFin.length, rows: term.rows,
            scrollTop: vpFin?.scrollTop, scrollHeight: vpFin?.scrollHeight, clientHeight: vpFin?.clientHeight,
            note: `mode=${mode} rh=${rowHeight.toFixed(2)}`,
          });
          if (pendingRestoreSeq === restoreToken) {
            pendingRestoreSeq = 0;
            snapshot();
          }
        });
      });
      return true;
    };
    // Initial snapshot so preDragRef has a baseline before any
    // user interaction or write — otherwise the first drag would
    // find preDragRef at its (0, 0, true) default.
    snapshot();

    // First fit — best-effort using whatever font metrics are currently
    // resolved. If our monospace stack ("JetBrains Mono", "SF Mono",
    // etc.) hasn't loaded yet, the browser falls back to a narrower
    // default font and xterm measures cells too narrow → too many cols.
    // The server then draws the TUI wider than fits on screen.
    //
    // We therefore re-fit once document.fonts.ready resolves and push
    // the corrected cols back to the agent. ResizeObserver alone doesn't
    // catch this case because the HOST ELEMENT's size never changed —
    // only the glyph metrics did.
    fitPreservingScroll();

    // Multi-pass refit for mobile font-loading races. On Android Chrome
    // specifically, fit.fit() at mount frequently measures cells too
    // narrow (monospace fallback not fully settled) and reports way
    // too many cols — e.g. 101 instead of 53 at 390px. Claude then
    // draws at 101, xterm wraps at 53. document.fonts.ready doesn't
    // help here because we don't @font-face our monospace stack, so
    // it resolves "immediately" with nothing to wait for, BEFORE the
    // system fallback font is actually ready for glyph measurement.
    //
    // Strategy: re-fit at 0, 150, 600, 1500ms. If any pass produces
    // different cols from the WS's last-reported size, push a resize
    // to the daemon so Claude gets a fresh SIGWINCH, then send Ctrl+L
    // (on mobile) to nudge TUIs to redraw at the corrected width.
    let lastReportedCols = term.cols;
    let lastReportedRows = term.rows;
    const refit = () => {
      if (disposed) return;
      try {
        if (!fitPreservingScroll()) return;
        if (term.cols === lastReportedCols && term.rows === lastReportedRows) return;
        lastReportedCols = term.cols;
        lastReportedRows = term.rows;
        const ws = wsRef.current;
        if (ws && ws.readyState === WebSocket.OPEN) {
          ws.send(JSON.stringify({ type: 'resize', cols: term.cols, rows: term.rows }));
          if (isPhoneWidth) {
            // Small extra delay so SIGWINCH reaches the agent/Claude
            // before the redraw hint lands.
            window.setTimeout(() => {
              if (disposed || !currentVisible()) return;
              const w = wsRef.current;
              if (w && w.readyState === WebSocket.OPEN) {
                w.send(encoder.encode('\x0c')); // Ctrl+L
              }
            }, 80);
          }
        }
      } catch { /* ignore */ }
    };
    const onEmbedVisible = () => requestAnimationFrame(() => requestAnimationFrame(refit));
    if (isEmbedded()) window.addEventListener('solu:embed-visible', onEmbedVisible);
    // Single deferred refit after fonts.ready resolves — covers
    // the font-not-loaded-yet race. We used to also fire at 150ms/
    // 600ms/1500ms for robustness, but each pass that actually
    // changed cols triggered another SIGWINCH on the server, which
    // made Claude redraw repeatedly — visible as flicker. One
    // fonts.ready pass + a 600ms safety net is enough.
    if (typeof document !== 'undefined' && document.fonts && document.fonts.ready) {
      document.fonts.ready.then(refit).catch(() => {});
    }
    window.setTimeout(refit, 600);

    // Post-paint refit — catches the class of bugs where fit.fit()
    // measured the host container mid-layout, before the browser
    // committed a paint, and ResizeObserver never fires afterwards
    // because the final size ends up matching the (wrong) measurement.
    // Symptoms differ by platform but share the same root cause:
    //   - Mobile: pane switch unmounts/remounts. If fit runs during
    //     the tab-bar transition or mobile chrome settling, xterm can
    //     extend past the visible viewport and clip the Claude input
    //     bar off-screen with no way to scroll to it.
    //   - Desktop: imperative PanelGroup.setLayout() from the ratio-
    //     restore path (v0.0.111), zoom toggle, or any layout-tree
    //     mutation can update panel sizes without pixel-dim change
    //     (sub-pixel rounding aligns to prior size) → no RO fire.
    //     Symptom: xterm fills only a short region of the pane until
    //     the user drags the splitter (which forces a real size change
    //     → RO fires → refit).
    // Double-rAF runs after at least one committed paint — the
    // canonical "wait for layout to settle" pattern. No-op if the
    // initial fit was already correct (refit guards on cols/rows
    // equality before any SIGWINCH).
    requestAnimationFrame(() => {
      if (disposed) return;
      requestAnimationFrame(() => {
        if (disposed) return;
        refit();
      });
    });

    // Rendering: xterm.js's default canvas/DOM renderer. We used to
    // offer an opt-in WebGL renderer (xterm-addon-webgl) but it was
    // removed because Chromium caps active WebGL contexts per tab
    // (~16) and soluterminal's multi-pane × multi-workspace usage
    // trivially blows past that cap — when contexts get evicted,
    // their texture atlases become invalid and cells render the
    // wrong glyphs ("Arabic-looking gibberish"). See
    // memory/feedback_webgl_context_limit.md for the saga. Canvas
    // has no such limit and no atlas; it's fast enough for terminal
    // workloads. If we ever need GPU rendering again, reintroduce
    // with a smart default that caps total contexts.

    // Right-click on the pane body is now owned by the outer pane
    // <div>'s onContextMenu prop — opens the Split/Clone/Rename/Close
    // menu. Pre-existing "smart right-click" (copy selection / paste
    // clipboard) was removed per user call.

    // Wheel throttle. In alt-screen mode (Claude and friends) xterm
    // forwards EVERY wheel event 1:1 as a mouse CSI sequence — a
    // single trackpad flick emits 20+ events and Claude interprets
    // each as "scroll one line", making scroll feel wildly fast.
    // Here we swallow events that arrive too close together on the
    // capture phase, before xterm sees them. 60ms min gap → ~15
    // events/sec max, which matches a comfortable read-scroll rate
    // on both trackpad and mouse wheel. scrollSensitivity (xterm
    // option) only affects its OWN scrollback; this handles the
    // alt-screen path the option can't touch.
    // Self-healing ydisp ↔ scrollTop sync — the root fix for the
    // "can't scroll back down until Jump-to-live" bug (repro'd via
    // Playwright + a ydisp write-trap, 2026-06-12).
    //
    // xterm's Viewport pins scrollTop programmatically on every refresh
    // (scrollTop = ydisp × rowHeight) and arms _ignoreNextScrollEvent so
    // its own pin doesn't echo back as a scroll. But DOM scroll events
    // COALESCE: when a user wheel write lands in the same frame as a
    // pin, the browser fires ONE merged scroll event, the armed flag
    // swallows it (Viewport.ts:190 → _scrollLines(0)), and the wheel's
    // delta never reaches ydisp — then the next refresh re-pins
    // scrollTop back to the old line, reverting the user's motion.
    // Anything that re-arms the flag steadily (pane resize churn from
    // the last-prompt strip / header while output streams) eats EVERY
    // wheel tick that way: scroll-down appears dead until Jump-to-live.
    //
    // xterm's own handler runs first (it attached at open()); we run
    // after it and apply any residual line diff ourselves, so a
    // swallowed event can never lose user scroll. Uses xterm's
    // _currentRowHeight (device-derived), NOT css.cell.height — they
    // differ fractionally at non-integer devicePixelRatio and the
    // mismatch would self-induce a multi-line drift at deep scrollback.
    const healViewportSync = () => {
      if(!canAct())return;
      const vpEl = readViewport();
      if (!vpEl || !vpEl.offsetParent) return; // hidden: geometry unreliable
      // While the reader is following the tail, a DOM scroll event is a reflow
      // artifact (scroll-area height change, xterm coalescing its own writes),
      // NOT a user scroll. Translating the stale pixel diff into scrollLines()
      // would set xterm's isUserScrolling latch and stop auto-follow for good —
      // the "drifts into history while output streams" bug. Pin instead.
      if (paneReaderMode.followTailRef.current) {
        if (vpEl.scrollTop + vpEl.clientHeight < vpEl.scrollHeight - 1) {
          vpEl.scrollTop = vpEl.scrollHeight;
        }
        return;
      }
      const core = withXtermCore();
      const rowHeight = core?.viewport?._currentRowHeight ?? 0;
      if (rowHeight <= 0) return;
      const diff = Math.round(vpEl.scrollTop / rowHeight) - term.buffer.active.viewportY;
      if (diff !== 0) term.scrollLines(diff);
    };
    let removeHealListener: (() => void) | null = null;
    requestAnimationFrame(() => {
      if (disposed) return;
      const vpEl = readViewport();
      if (!vpEl) return;
      vpEl.addEventListener('scroll', healViewportSync, { passive: true });
      removeHealListener = () => vpEl.removeEventListener('scroll', healViewportSync);
    });

    let lastWheelAt = 0;
    const onWheel = (e: WheelEvent) => {
      if(!canAct())return;
      const gestureValid=captureSessionGesture(session);
      // Before the throttle: every physical wheel notch — even ones the
      // throttle swallows — invalidates a pending resize restore and
      // re-baselines the restore anchor to wherever the scroll lands.
      rebaselineAfterUserScroll();
      const now = performance.now();
      if (now - lastWheelAt < 60) {
        e.preventDefault();
        e.stopImmediatePropagation();
        return;
      }
      lastWheelAt = now;
      // Wheel-intent ledger — the verified root fix for stuck scrollback.
      // A wheel notch can be erased with NO observable trace: xterm's
      // wheel handler applies scrollTop += amount, but when
      // Viewport._innerRefresh re-pins scrollTop in the same frame
      // (resize churn re-arms this constantly), the two writes cancel
      // and the browser emits no scroll event at all — so no scroll
      // listener can ever recover it. The wheel event here is the only
      // record of the user's intent. Verify two frames later (scroll
      // steps run before rAF callbacks, so xterm's normal path has
      // already landed by then) that the viewport moved; if it was
      // erased and we're not at a buffer boundary, drive the buffer
      // directly. Boundary guards make this inert on alt-screen apps
      // (baseY = 0) and at the scrollback edges.
      const bufAtWheel = term.buffer.active;
      const beforeY = bufAtWheel.viewportY;
      const dir = Math.sign(e.deltaY);
      const atEdge = (dir > 0 && beforeY >= bufAtWheel.baseY) || (dir < 0 && beforeY <= 0);
      if (dir !== 0 && !atEdge) {
        const rowH = withXtermCore()?.viewport?._currentRowHeight || 16;
        const sens = term.options.scrollSensitivity ?? 1;
        const lines = e.deltaMode === WheelEvent.DOM_DELTA_LINE
          ? Math.round(Math.abs(e.deltaY) * sens)
          : Math.round((Math.abs(e.deltaY) * sens) / rowH);
        if (lines >= 1) {
          requestAnimationFrame(() => requestAnimationFrame(() => {
            if (disposed || !gestureValid()) return;
            const bufNow = term.buffer.active;
            if (bufNow.viewportY !== beforeY) return; // wheel landed normally
            if (dir > 0 && bufNow.viewportY >= bufNow.baseY) return;
            if (dir < 0 && bufNow.viewportY <= 0) return;
            term.scrollLines(dir * lines);
            logScrollDiag({
              t: performance.now(),
              paneId: pane.id,
              label: 'wheel-intent-heal',
              ydisp: bufNow.viewportY, length: bufNow.length, rows: term.rows,
              note: `recovered ${dir > 0 ? '+' : '-'}${lines}`,
            });
          }));
        }
      }
    };
    hostRef.current.addEventListener('wheel', onWheel, { capture: true, passive: false });

    // Clipboard integration — matches what users expect from native
    // terminal emulators (gnome-terminal, iTerm2, Alacritty):
    //   Ctrl+C with a selection  → copy, swallow the event
    //   Ctrl+C without selection → pass through (SIGINT to the process)
    //   Ctrl+Shift+C             → always copy (if any selection)
    //   Ctrl+Shift+V             → paste (handled by xterm's native
    //                              paste-event listener — we don't
    //                              need a custom branch, and having
    //                              one caused a double-paste bug
    //                              because our handler ran AND the
    //                              browser's native paste event still
    //                              fired on xterm's textarea)
    // Returning false from the handler tells xterm to NOT forward the
    // key to the PTY.
    term.attachCustomKeyEventHandler((ev) => {
      if(!canAct())return false;
      if (ev.type !== 'keydown') return true;
      const gestureValid=captureSessionGesture(session);
      if (!handleTerminalCopyKey(ev, term, () => {if(gestureValid())useStore.getState().toast(
        'Copy failed — clipboard unavailable. Your text remains selected.', { kind: 'error', icon: '⚠' },
      );})) return false;
      // Keyboard scrollback nav — replaces reaching for the mouse wheel.
      // All shift-modified so the unshifted arrows / PageUp / Home still
      // reach the PTY (Claude message nav, vim scroll, less paging, etc.).
      // Returning false tells xterm "I handled this; don't send to PTY".
      if (ev.shiftKey && !ev.ctrlKey && !ev.altKey && !ev.metaKey) {
        // 3 lines per arrow press feels right — single-line is too slow,
        // full-page is too abrupt. Matches the sensitivity of a typical
        // mouse-wheel notch.
        // Keyboard scrollback nav is user scroll intent too — don't let a
        // pending resize restore yank the position afterwards.
        if (ev.key === 'ArrowUp') { rebaselineAfterUserScroll(); term.scrollLines(-3); return false; }
        if (ev.key === 'ArrowDown') { rebaselineAfterUserScroll(); term.scrollLines(3); return false; }
        if (ev.key === 'PageUp') { rebaselineAfterUserScroll(); term.scrollPages(-1); return false; }
        if (ev.key === 'PageDown') { rebaselineAfterUserScroll(); term.scrollPages(1); return false; }
        if (ev.key === 'Home') { rebaselineAfterUserScroll(); term.scrollToTop(); return false; }
        if (ev.key === 'End') { rebaselineAfterUserScroll(); term.scrollToBottom(); return false; }
      }
      return true;
    });

    termRef.current = term;
    lifecycleLog('pane.mount', {
      paneId: pane.id,
      backend: pane.backend,
      prefix: session.scope.prefix,
      visibility: document.visibilityState,
      focused: typeof document.hasFocus === 'function' ? document.hasFocus() : null,
    });

    const cleanupReaderMode = paneReaderMode.attachReaderMode(term);

    // Returning to the normal buffer from a full-screen (alt-screen) app —
    // vim / nano / less, Alt+G's $EDITOR, pagers — must land back at the
    // live prompt at the bottom, like a real terminal. xterm restores the
    // normal buffer's PRE-app ydisp on exit, so when the shell then streams
    // output (e.g. the edited command runs), it can sit above the new
    // bottom and never auto-follow — the viewport stays parked in history
    // until the user clicks Jump-to-live. Diagnosed from a live scrollDiag
    // trace: reader-away at yd=3380 while len grew to 4108, no fit/restore
    // events. Snap to bottom + clear the user-scroll latch so subsequent
    // writes follow. Deferred one frame so it runs after xterm's own
    // buffer-restore. Unconditional bottom-snap matches real terminals:
    // exiting a full-screen app never preserves your old scrollback spot.
    let forceFollowUntil = 0;
    const reassertLiveFollow = () => {
      try { term.scrollToBottom(); } catch { /* best-effort */ }
      // Clear the user-scroll latch AFTER scrollToBottom: xterm can re-arm
      // it inside its own scroll path, and a latch left set makes the NEXT
      // write skip auto-follow — which is exactly how the viewport got
      // parked in history.
      const core = withXtermCore();
      if (core?.bufferService) core.bufferService.isUserScrolling = false;
    };
    const bufferChangeDisp = term.buffer.onBufferChange(() => {
      if (term.buffer.active.type !== 'normal') return;
      // A one-shot snap lands at the (then-near-empty) prompt; the edited
      // command's output then streams in over the next frames and scrolls
      // the view back into history. So hold a short follow-lock: re-pin to
      // bottom on every write in that post-exit burst. Once xterm's native
      // follow is healthy again (ydisp==baseY, latch clear) it carries on
      // after the window closes.
      forceFollowUntil = performance.now() + 1500;
      requestAnimationFrame(() => {
        if (disposed) return;
        reassertLiveFollow();
        logScrollDiag({
          t: performance.now(), paneId: pane.id, label: 'altexit-follow',
          ydisp: term.buffer.active.viewportY, length: term.buffer.active.length, rows: term.rows,
        });
      });
    });
    const followAfterReturnDisp = term.onWriteParsed(() => {
      if (performance.now() > forceFollowUntil) return;
      // Respect explicit user scroll intent: apps like Claude Code's Ink TUI
      // re-enter/exit the alt-screen every turn, re-arming this follow-lock
      // window on each exit. Without this guard, a user scrolled up into
      // scrollback gets yanked back to the bottom on the next write. Only
      // reassert follow when the user has NOT scrolled away from the bottom.
      const core = withXtermCore();
      if (core?.bufferService?.isUserScrolling) return;
      reassertLiveFollow();
    });

    // Expose a snapshot getter so voice-to-text can ask "what is the
    // user currently looking at?" and feed that as context to the
    // cleanup LLM. Unregistered alongside the sender on unmount below.
    registerPaneSnapshot(pane.id, () => {
      const buf = term.buffer.active;
      const total = buf.length;
      const take = Math.min(50, total);
      const out: string[] = [];
      for (let i = total - take; i < total; i++) {
        const line = buf.getLine(i);
        if (line) out.push(line.translateToString(true));
      }
      return out.join('\n').trim();
    });

    const encoder = new TextEncoder();
    let reconnectAttempt = 0;
    let reconnectTimer: number | null = null;
    let resizeRefreshTimer: number | null = null;
    let restoreRepaintPending = false;
    let openedOnce = false;
    let suppressResizeRepairUntil = 0;
    let skipNextRestoreReplay = false;
    // Exact-resume bookkeeping. ringOffset mirrors the daemon ring's
    // TotalWritten as of the last byte this client APPLIED; ringEpoch
    // ties it to one daemon process lifetime (ring offsets reset on
    // daemon restart). On a skip-replay reconnect we send both, and
    // the daemon replays precisely the bytes we missed — byte-exact,
    // no grid-model repaint, no ghost text (the v0.0.509 input-row
    // ghost came from model drift in those repaints). -1 = no
    // baseline (fresh mount or pre-offset daemon) → legacy behavior.
    let ringOffset = -1;
    let ringEpoch = 0;
    let lastRestoreBackgroundAt = 0;
    let reclaimOnRestoreReconnect = false;
    let pendingRestoreReconnect = false;
    let heldForUpdateReconnect = false;
    const isDesktopApp = !isEmbedded() && typeof window !== 'undefined'
      && !!(window as unknown as { __SOLU_TAURI__?: boolean }).__SOLU_TAURI__;

    const markRestoreBackgrounded = (source = 'unknown') => {
      lastRestoreBackgroundAt = Date.now();
      skipNextRestoreReplay = true;
      if (ownedRef.current === true) {
        reclaimOnRestoreReconnect = true;
      }
      debugLog('[solu] restore backgrounded', { paneId: pane.id, source, cloud: !!session.scope.prefix });
      lifecycleLog('pane.restore-backgrounded', {
        paneId: pane.id,
        source,
        cloud: !!session.scope.prefix,
        owned: ownedRef.current,
        wsReadyState: wsRef.current?.readyState ?? null,
      });
    };

    const recentlyRestoreBackgrounded = () =>
      lastRestoreBackgroundAt > 0 && Date.now() - lastRestoreBackgroundAt < 5000;

    const isRestoreBackgrounded = () =>
      skipNextRestoreReplay || recentlyRestoreBackgrounded();

    const shouldHoldCloudRestoreReconnect = () =>
      isDesktopApp
      && !!session.scope.prefix
      && (
        isRestoreBackgrounded()
        || (typeof document !== 'undefined' && document.visibilityState !== 'visible')
        || (typeof document !== 'undefined' && typeof document.hasFocus === 'function' && !document.hasFocus())
      );

    const nudgeRestorePaint = () => {
      const gestureValid=captureSessionGesture(session);
      if(!gestureValid())return;
      window.requestAnimationFrame(() => {
        window.requestAnimationFrame(() => {
          if (disposed || !gestureValid()) return;
          try {
            term.refresh(0, Math.max(0, term.rows - 1));
          } catch { /* renderer may already be disposed */ }
          if (effectiveTerminalTarget(useStore.getState()) === pane.id && !isMobileViewport()
              // A WebView2 reconnect completing must not yank the caret back here
              // if the user has since moved on to type in another pane's composer.
              && !isTypingElsewhere(term.textarea ?? null)) {
            // Desktop only — see the focus effect above. Auto-refocusing on
            // mobile re-summons the keyboard + viewport pan on every reconnect.
            try { term.focus(); } catch { /* best-effort */ }
          }
        });
      });
    };

    // Catch-up veil plumbing. Begin covers the pane with an opaque layer
    // (CSS .pane-catchup) so the user doesn't watch xterm fast-scroll
    // through a large replay; end fades it out. A safety timer clears a
    // veil whose replay never completes (truncated stream, dead socket),
    // and onclose ends it too — a stuck black pane would be worse than
    // a visible catch-up.
    let catchupSafetyTimer: number | null = null;
    let catchupFadeTimer: number | null = null;
    const endCatchup = () => {
      if (catchupSafetyTimer !== null) { window.clearTimeout(catchupSafetyTimer); catchupSafetyTimer = null; }
      if (disposed || !canAct()) {setCatchup(null);return;}
      setCatchup((c) => (c === 'active' ? 'fading' : c));
      if (catchupFadeTimer !== null) window.clearTimeout(catchupFadeTimer);
      catchupFadeTimer = window.setTimeout(() => {
        catchupFadeTimer = null;
        if (!disposed) setCatchup(null);
      }, 260);
    };
    const beginCatchup = () => {
      if (disposed || !canAct()) return;
      if (catchupFadeTimer !== null) { window.clearTimeout(catchupFadeTimer); catchupFadeTimer = null; }
      setCatchup('active');
      if (catchupSafetyTimer !== null) window.clearTimeout(catchupSafetyTimer);
      catchupSafetyTimer = window.setTimeout(endCatchup, 6000);
    };

    // One-shot post-attach redraw nudge for PTYs spawned at unverified dims
    // (armed in connect(), fired in ws.onopen once the attach resize is sent).
    let dimsUntrustedNudgePending = false;

    // We keep a single xterm instance across reconnects, but a new
    // WebSocket always starts with the daemon replay snapshot. On the
    // first attach, writing that replay into an empty terminal is correct.
    // On later reconnects, appending it to the existing xterm buffer
    // duplicates Codex's normal-buffer transcript ("multiple input boxes").
    // The daemon sends a replay-start control frame before the snapshot so
    // reconnects can reset xterm and then restore exactly one copy from the
    // daemon ring buffer. Minimize/restore is different: WebView2 may close
    // the socket while hidden, and replaying on restore makes every pane
    // visibly refresh. In that case we keep the current xterm surface and
    // discard just the daemon replay snapshot.
    let cleanCloseViewer = () => {};
    const unregisterCleanClose = registerTerminalCloseGuard(key, () => cleanCloseViewer());
    const onRetirementPageHide = () => {
      cleanCloseViewer();
      try { wsRef.current?.close(); } catch { /* page is closing */ }
    };
    window.addEventListener('pagehide', onRetirementPageHide, { capture: true });
    // signedUrl is set on the second pass when the stream had to be signed
    // first (approved devices: lib/deviceIdentity.ts).
    const connect = (signedUrl?: string) => {
      if (disposed || session.invalid || session.principal !== routingPrincipalEpoch()) return;
      if (session.scope.prefix && session.scope.key !== currentRoutingScope().key) { pendingRestoreReconnect = true; return; }
      pendingRestoreReconnect = false;
      setConnStatus(reconnectAttempt === 0 ? 'connecting' : 'reconnecting');
      const { cols, rows } = term;
      // What the daemon will align its reattach repaint to (sent below).
      const announcedTerm = { cols, rows };
      const connectRect = readUsableHostRect('ws-connect');
      // Attach-size seed: prefer the daemon's CURRENT PTY width over this
      // mount's fit. fit.fit() can measure the host mid-layout (warm-host
      // portal re-adoption, PanelGroup ratio-restore not yet applied, web
      // fonts not settled) and yield a transient-narrow width. Sending that
      // as the attach size SHRINKS the shared PTY; Claude then hard-wraps at
      // it, and those hard newlines can NEVER reflow when the layout settles
      // wide — the "narrow scrollback above, wide below" artifact, baked
      // permanently into the daemon's width-unaware ring. Seeding with the
      // daemon's existing width makes attach a sizing no-op; the settled
      // refit()/ResizeObserver pass sends the real measured width once (a
      // clean widen, never a transient shrink). Falls back to the local fit
      // only when the daemon width is unknown (brand-new pane).
      // UNVERIFIED dims are excluded from the seed: right after a daemon
      // restart (auto-update), the daemon's cols/rows are the persisted copy
      // from panes.json — often weeks stale (observed: 283×62 persisted vs
      // 67×29 real). Seeding with those resized the REAL PTY to the stale
      // width; the TUI repainted at it into every normal-width surface and
      // every pane came back garbled after each update. When unverified,
      // fall back to this mount's measured fit — the daemon adopts it as
      // truth on arrival.
      const liveDims = session.pane;
      const dimsTrusted = !!liveDims && !liveDims.dimsUnverified;
      // Arm the one-shot post-attach redraw nudge (sent in ws.onopen): when the
      // daemon spawned this PTY at UNVERIFIED dims (mode switch, resume, boot
      // restore — no live client measurement existed), the TUI's first paint
      // happened at a possibly-stale width. Our attach resize corrects the PTY,
      // but the already-painted frame stays mis-wrapped until a redraw. Phones
      // get a Ctrl+L from refit(); desktop had NO nudge — the "out-of-format
      // until manual Realign" bug after a Focus→Terminal switch.
      if (liveDims?.dimsUnverified) dimsUntrustedNudgePending = true;
      const seedCols = dimsTrusted && liveDims.cols > 0 ? liveDims.cols : 0;
      const seedRows = dimsTrusted && liveDims.rows > 0 ? liveDims.rows : 0;
      const fitCols = connectRect && cols > 0 ? cols : lastGoodFit.cols;
      const fitRows = connectRect && rows > 0 ? rows : lastGoodFit.rows;
      const connectCols = seedCols || fitCols;
      const connectRows = seedRows || fitRows;
      // Make the settled refit() resend relative to the SEED, not this
      // mount's fit: if the real measured width differs from what we seeded
      // the daemon with, refit must push it. (Otherwise a correct mount fit
      // that happens to equal the daemon's stale width would compare equal to
      // lastReportedCols and never be sent — leaving the pane stuck at the
      // seed.)
      lastReportedCols = connectCols;
      lastReportedRows = connectRows;
      const isDesktopCloudReconnect = openedOnce && isDesktopApp && !!session.scope.prefix;
      // Mobile exact-resume. A foreground network blip on a phone reconnects
      // with openedOnce=true but (historically) skipRestoreReplay=false →
      // full term.reset()+replay → the diff-replay-disease gibberish (mid-
      // animation jumble on normal-buffer TUIs). The daemon already supports
      // byte-exact resume via since/epoch (desktop uses it); enable it on
      // mobile whenever we hold a valid ring baseline. If the daemon can't
      // honor it (ring evicted / epoch mismatch) it replies resume:false with
      // an offset → the forceReplace path does one clean full replay. We
      // require an already-opened socket (openedOnce) and a real baseline
      // (ringOffset >= 0), so the very first attach still does a full replay.
      // Treat as a phone client only when NOT the desktop/Tauri app — a narrow
      // desktop window is < 800px wide but is not a mobile client.
      const isMobileClient = isPhoneWidth && !isDesktopApp;
      const isMobileResumeReconnect = openedOnce && isMobileClient && ringOffset >= 0;
      const skipRestoreReplay =
        openedOnce && (isRestoreBackgrounded() || isDesktopCloudReconnect || isMobileResumeReconnect);
      const replaceReplay = openedOnce && !skipRestoreReplay;
      lifecycleLog('pane.ws.connect', {
        paneId: pane.id,
        cols: connectCols,
        rows: connectRows,
        termCols: cols,
        termRows: rows,
        openedOnce,
        isDesktopCloudReconnect,
        skipRestoreReplay,
        replaceReplay,
        reconnectAttempt,
        cloud: !!session.scope.prefix,
        visibility: document.visibilityState,
        focused: typeof document.hasFocus === 'function' ? document.hasFocus() : null,
      });
      // PTY sizing is now driven by the pane's owner sub (see
      // daemon/pane.go Pane.ownerSubID). The WebSocket URL no longer
      // carries a force flag — first-to-connect auto-claims, and
      // later clients show an overlay with a "Take over" button.
      const streamUrl = signedUrl ?? api.wsUrl(pane.id, connectCols, connectRows, {
        skipReplay: skipRestoreReplay,
        since: skipRestoreReplay && ringOffset >= 0 ? ringOffset : undefined,
        epoch: skipRestoreReplay && ringOffset >= 0 ? ringEpoch : undefined,
        mobile: isMobileClient, scope:session.scope, visible:currentVisible(),
        termCols: cols > 0 ? cols : undefined, termRows: rows > 0 ? rows : undefined,
        retirementViewerId: pane.role === 'task_owner' ? terminalRetirementViewerId() : undefined,
      });
      // A machine this device enrolled with wants the stream signed. Signing
      // is async (the key is non-extractable WebCrypto), so sign and come
      // back; everything above is plain recomputation and safe to repeat.
      // With the private relay channel on for this machine the socket rides
      // the channel (lib/privateRelay) and only the channel. Checked even
      // for an already-signed URL, so a toggle turned on while signing can't
      // let this connect over the plaintext relay.
      const viaPrivateRelay = privateRelaySocketsFor(session.scope);
      if (!signedUrl && !viaPrivateRelay && streamSigningNeeded(session.scope)) {
        void signStreamUrl(streamUrl, session.scope).then((url) => connect(url));
        return;
      }
      const ws = viaPrivateRelay
        ? openWebSocket(streamUrl, api.wsProtocols(), session.scope)
        : new WebSocket(streamUrl, api.wsProtocols());
      // One transport choke point covers every terminal input/claim/geometry
      // path, including xterm protocol replies and delayed callbacks. Hidden
      // viewers retain output parsing and keepalive, never input authority.
      const transportSend = ws.send.bind(ws);
      const connectionIdentity = session.processIdentity;
      const connectionPrincipal = session.principal;
      let viewerClosing = false;
      const retirementValid = () => !disposed && wsRef.current === ws && ws.readyState === WebSocket.OPEN
        && !session.invalid && session.processIdentity === connectionIdentity
        && processIdentity(session.pane) === connectionIdentity
        && session.principal === connectionPrincipal && connectionPrincipal === routingPrincipalEpoch() && routingPrincipalAllowed();
      ws.send = (data) => {
        if (viewerClosing || !routingPrincipalAllowed() || session.invalid || session.principal !== routingPrincipalEpoch()) return;
        if (typeof data === 'string') {
          let type = ''; try {type = JSON.parse(data).type;} catch {return;}
          if (type === 'visibility') { transportSend(JSON.stringify({type,visible:currentVisible()})); return; }
          if (type === 'owner-retirement-ack') { transportSend(data); return; }
          if (type !== 'ping' && !currentVisible()) return;
        } else {
          if (!currentVisible() || ownedRef.current !== true) return;
          const bytes = data instanceof ArrayBuffer ? new Uint8Array(data) : ArrayBuffer.isView(data) ? new Uint8Array(data.buffer, data.byteOffset, data.byteLength) : null;
          if (bytes && holdTerminalInput(key, bytes)) return;
          if (!terminalInputAllowed(key)) { cancelTerminalRetirement(key); return; }
        }
        transportSend(data);
      };
      ws.binaryType = 'arraybuffer';
      wsRef.current = ws;

      let replayActive = false;
      let replayResetReady = false;
      let replayIsResume = false;
      let replayFlushing = false;
      let replayRemaining = 0;
      let skipReplayRemaining = 0;
      let replayChunks: Uint8Array[] = [];
      let pendingLiveWrites: Array<string | Uint8Array> = [];
      const localRetirementPending = () => replayActive || replayFlushing || pendingLiveWrites.length > 0 || ws.bufferedAmount > 0
        || terminalHasPendingInteraction(key) || !!terminalRecoveredInput(recoveryKey)
        || !!term.textarea?.value || quickReplyHasPendingInteraction(key, connectionIdentity)
        || paneDictating(pane.id);
      cleanCloseViewer = () => {
        if (pane.role !== 'task_owner' || viewerClosing || !retirementValid()
          || !terminalInputAllowed(key) || localRetirementPending()) return;
        // This exact page has no deferred delivery. No later callback may add
        // input to this connection after its final clean-close attestation.
        viewerClosing = true;
        transportSend(JSON.stringify({type: 'owner-viewer-clean-close', ready: true}));
      };
      let autoClaimPending = false;
      // True while the pending claim is a CONDITIONAL kind the daemon may
      // DENY: adopt-unowned, and (since claim arbitration) first-open /
      // reconnect — any automatic claim against a live owner whose user is
      // present. A denial acks with owner:"other", which must settle us
      // into the locked state instead of being suppressed forever. Only
      // explicit "takeover" is unconditional now.
      let autoClaimConditional = false;
      // The daemon writes the subscribe-time ownership frame BEFORE it can
      // have processed any claim we sent at onopen (ordered socket), so the
      // FIRST frame is always pre-claim state — never a denial ack. Without
      // this marker, a lingering same-device ghost's owner:"other" initial
      // frame would read as a denial and flash the lock overlay on every
      // reload, even though the claim is about to be granted.
      let sawInitialOwnershipFrame = false;
      // Stateful OSC color-query stripper threaded through the replay
      // chunks (which can split a sequence at any byte boundary). See
      // lib/oscStrip.ts for why this is necessary — short version: a
      // historical "ESC ] 11 ; ? ESC \" in the buffer would make
      // xterm auto-reply to a TUI that's no longer there, and the
      // reply would land at the bash prompt as visible gibberish.
      let replayStripState = newOscStripState();

      const writeQueued = (items: Array<string | Uint8Array>, done: () => void) => {
        const next = () => {
          const item = items.shift();
          if (item === undefined) {
            done();
            return;
          }
          term.write(item, next);
        };
        next();
      };

      const flushReplayIfReady = () => {
        if (!replayActive || !replayResetReady || replayRemaining > 0 || replayFlushing) return;
        replayFlushing = true;
        const chunks = replayChunks;
        replayChunks = [];
        const pinTarget = replayPinTarget(replayIsResume, announcedTerm, {
          cols: term.cols,
          rows: term.rows,
        });
        if (pinTarget) {
          replayPin = pinTarget;
          lifecycleLog('pane.ws.replay-pin', {
            paneId: pane.id,
            from: { cols: term.cols, rows: term.rows },
            to: pinTarget,
          });
          try { term.resize(pinTarget.cols, pinTarget.rows); } catch { /* best-effort */ }
        }
        const endReplayAnswers = replayAnswersRef.current.begin(replayIsResume);
        writeQueued(chunks, () => {
          endReplayAnswers();
          replayActive = false;
          replayFlushing = false;
          if (replayPin) {
            replayPin = null;
            refit();
          }
          const host = hostRef.current;
          if (host) applyTerminalTheme(term, host, resolveTerminalTheme(useStore.getState()));
          // Land at the latest content. During the (veiled) replay parse
          // xterm's viewport followed intermediate writes; the user's
          // mental model of a freshly-(re)attached pane is "show me the
          // newest output", same as a real terminal reattach. Exact
          // resumes are different: the surface was never replaced, so
          // they behave like ordinary live output — follow if at
          // bottom, stay put if the user is reading scrollback.
          if (!replayIsResume) {
            try { term.scrollToBottom(); } catch { /* best-effort */ }
            try {
              term.refresh(0, Math.max(0, term.rows - 1));
            } catch { /* best-effort renderer nudge */ }
          }
          const live = pendingLiveWrites;
          pendingLiveWrites = [];
          for (const item of live) term.write(item);
          if (canAct()) markActivity(pane.id);
          endCatchup();
        });
      };

      const writeOrQueueLive = (data: string | Uint8Array) => {
        if (replayActive || replayFlushing) {
          pendingLiveWrites.push(data);
          return;
        }
        term.write(data);
        if (canAct()) markActivity(pane.id);
      };

      ws.onopen = () => {
        lifecycleLog('pane.ws.open', {
          paneId: pane.id,
          skipRestoreReplay,
          replaceReplay,
          reclaimOnRestoreReconnect,
        });
        setConnStatus('open');
        reconnectAttempt = 0;
        const isFirstOpen = !openedOnce;
        openedOnce = true;
        if (skipRestoreReplay) {
          skipNextRestoreReplay = false;
        }
        if (skipRestoreReplay) {
          nudgeRestorePaint();
          scheduleRestoreRefit('ws-open-skip-replay');
        }
        // Re-assert the ATTACH SEED (daemon's current width), not a fresh
        // term measurement — at ws-open the host can still be mid-layout, and
        // re-measuring here was a second route for a transient-narrow width to
        // shrink the PTY. The settled refit()/ResizeObserver pass sends the
        // real measured width once, shortly after.
        ws.send(JSON.stringify({ type: 'resize', cols: connectCols, rows: connectRows }));
        // Initial visibility — send the current state so the daemon
        // knows whether to count this sub's cols toward the PTY size.
        // Backgrounded tabs don't get a vote; that way a PC tab the
        // user isn't looking at can't reflow the phone's terminal
        // (and vice versa).
        ws.send(
          JSON.stringify({
            type: 'visibility',
            visible: currentVisible(),
          }),
        );
        // Self-heal shared-PTY width drift on a RECONNECT (app-update reattach,
        // resume respawn, network blip): while we were gone the daemon's width
        // may have been driven by a restart or a peer, and our host pixel-size
        // didn't change — so nothing else would re-send our measured width. A
        // first open needs none: the attach seed already carries the right width.
        if (!isFirstOpen) {
          realign('ws-reopen');
        }
        // Dims-unverified mounts (Focus→Terminal switch, resume, boot restore):
        // the attach resize above just corrected the PTY from its stale spawn
        // width, but the TUI's already-painted frame stays mis-wrapped. Send a
        // one-shot Ctrl+L (the same nudge phones get from refit()) after a
        // short delay so the SIGWINCH lands before the redraw hint. Cleared on
        // fire — reconnects don't re-nudge unless connect() re-armed it.
        if (dimsUntrustedNudgePending) {
          dimsUntrustedNudgePending = false;
          window.setTimeout(() => {
            if (disposed) return;
            const w = wsRef.current;
            if (w && w.readyState === WebSocket.OPEN) {
              w.send(encoder.encode('\x0c')); // Ctrl+L
            }
          }, 150);
        }
        registerSender(pane.id, (bytes) => {
          if (viewerClosing) return false;
          if (!terminalInputAllowed(key)) { cancelTerminalRetirement(key); return false; }
          if (ws.readyState !== WebSocket.OPEN || !currentVisible() || ownedRef.current !== true) return false;
          resumeFollowIfNearBottom();
          ws.send(typeof bytes === 'string' ? encoder.encode(bytes) : bytes);
          return true;
        });
        // Claimer fires {type:"claim"} on THIS pane's WS. Centralising
        // via store lets "Take over" claim every pane at once.
        registerClaimer(pane.id, () => {
          if (ws.readyState !== WebSocket.OPEN) return;
          ws.send(JSON.stringify({ type: 'claim', reason: 'takeover' }));
        });
        // Redrawer fires {type:"redraw"} — user-triggered from the
        // pane-header button or keybinding. Daemon-side this does
        // a screen-clear + size-bump so Ratatui-based TUIs (codex)
        // emit a fresh full frame after ghost cells appear post-
        // resize / post-workspace-switch. Never auto-invoked.
        //
        // term.reset() was added in v0.0.200 to address cross-click
        // inconsistency and then REMOVED in v0.0.202: the real
        // cause of that inconsistency was the daemon-side rows-
        // drift bug (v0.0.201 single-flight gate + owner-sub
        // target), not xterm state-machine residue. And
        // term.reset() has a side-effect the user caught: it
        // wipes xterm's SCROLLBACK buffer entirely, so past chat /
        // command output visible above the input widget doesn't
        // just go off-viewport — it's permanently gone. Relying
        // on the daemon's \x1b[2J\x1b[H inject alone preserves
        // scrollback (that escape only clears visible cells).
        registerRedrawer(pane.id, () => {
          if (ws.readyState !== WebSocket.OPEN) return;
          ws.send(JSON.stringify({ type: 'redraw' }));
        });
        // Realigner fires the width self-heal on demand — user-triggered from
        // the pane-header "Realign" button / keybinding, and by "Realign all".
        // Unlike redraw (repaint only, same width), this re-stamps active
        // sizing and force-resends the measured width, so it fixes a PTY-width
        // MISMATCH — the post-update / cross-device garble — not just ghost
        // cells. It is the one-press equivalent of the open/close-browser trick.
        registerRealigner(pane.id, () => {
          // The user explicitly wants THIS on-screen device to render correctly,
          // so grab sizing (win the election even against an active peer), then
          // force-resend our width and request a clean clamped frame.
          sendActiveSizing();
          realign('user');
          requestClampedRepaint();
        });
        // Auto-claim policy (server does NOT auto-claim anymore —
        // every ownership change is client-driven, see Subscribe
        // in daemon/pane.go):
        //   - Driven browsers (navigator.webdriver — Playwright, E2E
        //     suites, MCP-held browsers) NEVER auto-claim. Each fresh
        //     test context has empty localStorage → a brand-new
        //     deviceId, and its first-open claims were silently
        //     stealing every rendered pane from the human's desktop
        //     ("in use somewhere else" with no second device in
        //     sight). Tests that need ownership click Take over.
        //   - First open on desktop: auto-claim. A user opening
        //     the app on a full-size browser is clearly intending
        //     to use the session as the single-device default. The
        //     daemon arbitrates: it denies this claim if another
        //     device's user is at their screen (their overlay wins).
        //   - Reconnects: do NOT re-auto-claim. Tauri WebView2 in
        //     particular reopens pane WS frequently (visibility,
        //     resize, network blips), and unconditional reclaim
        //     made it impossible for any other viewer's takeover
        //     to stick — Tauri would silently grab ownership
        //     back within ms. Reconnects must preserve whoever
        //     the daemon currently considers owner.
        //   - Mobile: auto-claim ONLY when claimIntent is true —
        //     i.e. after the user has explicitly tapped "Take
        //     over" on this browser. Otherwise mobile stays
        //     passive (overlay shown by PaneGrid) so pane switches
        //     can't silently steal ownership from PC.
        //   - claimIntent path: a user who explicitly tapped
        //     "Take over" on this browser keeps reclaiming on
        //     WS open until they're displaced (which resets
        //     claimIntent in setPaneOwned) — but only while a
        //     human is actually here (page visible + a recent
        //     gesture). An idle-but-open laptop or pocketed phone
        //     cycling on relay socket timeouts must not re-take
        //     panes from the device the user is really on.
        const isAutomation = typeof navigator !== 'undefined' && navigator.webdriver === true;
        const claimIntentActive =
          useStore.getState().claimIntent && currentVisible() && userRecentlyActive();
        const explicitTakeover = (isFirstOpen && !isPhoneWidth) || claimIntentActive;
        const reconnectReclaim = isDesktopApp && reclaimOnRestoreReconnect;
        const shouldAutoClaim = !isAutomation && (explicitTakeover || reconnectReclaim);
        reclaimOnRestoreReconnect = false;
        if (shouldAutoClaim) {
          // A pure reconnect reclaim re-asserts INPUT ownership but must not
          // re-stamp the active-sizing device — otherwise a desktop's frequent
          // WebView2 reconnects keep stealing the PTY width back from a phone
          // the user is actively viewing (the 84↔49 thrash). A first-open /
          // explicit "Take over" still stamps (its geometry should win).
          const claimMsg =
            reconnectReclaim && !explicitTakeover
              ? { type: 'claim', reason: 'reconnect' }
              : {
                  type: 'claim',
                  reason: isFirstOpen && !claimIntentActive ? 'first-open' : 'takeover',
                };
          autoClaimPending = true;
          // Everything except an explicit takeover is now arbitrated by the
          // daemon and can be DENIED (a live owner whose user is present
          // keeps the pane). A denial acks with owner:"other" — it must
          // settle us into the truthful locked state, not be suppressed as
          // a handshake race.
          autoClaimConditional = claimMsg.reason !== 'takeover';
          ws.send(JSON.stringify(claimMsg));
        } else if (ownedRef.current === true) {
          // We were this pane's owner when the connection dropped, on a path
          // the restore-reconnect marker never sees — above all the daemon
          // UPDATE RESTART (frequent with install-when-idle), which wipes
          // ownership server-side and used to lock EVERY pane behind a false
          // "in use somewhere else" overlay. Re-adopt CONDITIONALLY: the
          // daemon grants adopt-unowned only if nobody owns the pane now, so
          // unlike reason:"reconnect" this can never undo a takeover that
          // happened while we were disconnected — if a peer really took
          // over, the denial ack (owner:"other") lands us in the truthful
          // locked state.
          autoClaimPending = true;
          autoClaimConditional = true;
          ws.send(JSON.stringify({ type: 'claim', reason: 'adopt-unowned' }));
        }
        if (skipRestoreReplay && hasCodexRef.current) {
          window.setTimeout(() => {
            if (disposed) return;
            if (ws.readyState === WebSocket.OPEN) {
              ws.send(JSON.stringify({ type: 'redraw' }));
            }
          }, 50);
        }
        // Single Ctrl+L redraw hint on mobile at ~500ms post-open
        // — after the fonts.ready refit has landed so Claude has
        // the correct cols. Previously we sent a second volley at
        // 1200ms "for reliability", but the extra SIGWINCH caused
        // Claude to redraw AGAIN, which looked like flicker. One
        // well-timed volley is better than two.
        if (isPhoneWidth) {
          window.setTimeout(() => {
            if (disposed) return;
            if (ws.readyState === WebSocket.OPEN) {
              ws.send(encoder.encode('\x0c')); // Ctrl+L
            }
          }, 500);
        }
      };
      ws.onmessage = (ev) => {
        if (viewerClosing || disposed || session.invalid || wsRef.current !== ws || session.principal !== routingPrincipalEpoch()) return;
        if (ev.data instanceof ArrayBuffer) {
          const bytes = new Uint8Array(ev.data);
          if (skipReplayRemaining > 0) {
            if (bytes.byteLength <= skipReplayRemaining) {
              skipReplayRemaining -= bytes.byteLength;
              return;
            }
            const tail = bytes.slice(skipReplayRemaining);
            skipReplayRemaining = 0;
            writeOrQueueLive(tail);
            return;
          }
          if (replayActive) {
            if (replayRemaining > 0) {
              if (bytes.byteLength <= replayRemaining) {
                // Decrement the remaining counter against the RAW
                // byte count (server-reported), not the post-strip
                // count — otherwise we'd over-consume the stream.
                replayRemaining -= bytes.byteLength;
                replayChunks.push(stripOscColorQueries(bytes, replayStripState));
              } else {
                const head = bytes.slice(0, replayRemaining);
                const tail = bytes.slice(replayRemaining);
                replayRemaining = 0;
                replayChunks.push(stripOscColorQueries(head, replayStripState));
                // The tail is post-cut live output — counts toward
                // the ring offset (the replay itself is covered by
                // the offset baseline from replay-start).
                if (ringOffset >= 0) ringOffset += tail.byteLength;
                pendingLiveWrites.push(tail);
              }
              flushReplayIfReady();
            } else {
              if (ringOffset >= 0) ringOffset += bytes.byteLength;
              pendingLiveWrites.push(bytes);
            }
            return;
          }
          if (ringOffset >= 0) ringOffset += bytes.byteLength;
          writeOrQueueLive(bytes);
        } else if (typeof ev.data === 'string') {
          // Server text frames carry control messages (JSON) — not
          // PTY bytes. Currently only ownership changes; detect by
          // attempting to parse JSON with a known type and fall
          // back to writing as text if that fails.
          try {
            const msg = JSON.parse(ev.data) as {
              type?: string; owned?: boolean; owner?: string; bytes?: number;
              offset?: number; epoch?: number; resume?: boolean; token?: string; expiresAtMs?: number; leaseMs?: number;
            };
            if (msg.type === 'owner-retirement-probe') {
              if (typeof msg.token !== 'string') return;
              const token = msg.token;
              const ready = beginTerminalRetirement(key, { token, recoveryKey, expiresAtMs: msg.expiresAtMs, leaseMs: msg.leaseMs, valid: retirementValid,
                pending: localRetirementPending,
                cancel: () => { if (retirementValid()) transportSend(JSON.stringify({type: 'owner-retirement-ack', token, ready: false, reason: 'input started'})); },
                flush: bytes => { if (!retirementValid() || !currentVisible() || ownedRef.current !== true) return false; transportSend(bytes); return true; },
              });
              transportSend(JSON.stringify({type: 'owner-retirement-ack', token, ready, reason: ready ? '' : 'pending interaction or invalid lease'}));
              return;
            }
            if (msg.type === 'owner-retirement-release') {
              if (typeof msg.token === 'string') releaseTerminalRetirement(key, msg.token);
              return;
            }
            if (msg.type === 'replay-start') {
              const replayBytes = msg.bytes ?? 0;
              const hasOffset = typeof msg.offset === 'number' && typeof msg.epoch === 'number';
              lifecycleLog('pane.ws.replay-start', {
                paneId: pane.id,
                bytes: replayBytes,
                resume: msg.resume === true,
                offset: msg.offset,
                skipRestoreReplay,
                replaceReplay,
                cloud: !!session.scope.prefix,
              });
              if (msg.resume === true) {
                // Exact resume: the daemon is sending precisely the
                // bytes we missed during the disconnect. Apply them in
                // place — no reset, no scroll yank — and adopt the
                // post-slice offset as the new counting baseline.
                skipNextRestoreReplay = false;
                if (hasOffset) {
                  ringOffset = msg.offset!;
                  ringEpoch = msg.epoch!;
                }
                if (replayBytes > 0) {
                  replayActive = true;
                  replayIsResume = true;
                  replayResetReady = true; // surface kept; nothing to reset
                  replayFlushing = false;
                  replayRemaining = replayBytes;
                  replayChunks = [];
                  pendingLiveWrites = [];
                  replayStripState = newOscStripState();
                  if (replayBytes >= CATCHUP_VEIL_MIN_BYTES) {
                    beginCatchup();
                  }
                }
                return;
              }
              // resume === false with an offset means we ASKED to
              // resume but the daemon couldn't (ring evicted the gap /
              // daemon restarted): replace the stale surface with the
              // full replay rather than silently keeping it. Without
              // an offset this is a legacy daemon: keep the old
              // discard-the-replay behavior.
              const forceReplace = skipRestoreReplay && hasOffset;
              if (skipRestoreReplay && !forceReplace) {
                skipNextRestoreReplay = false;
                if (replayBytes > 0) {
                  debugLog('[solu] restore replay skipped', {
                    paneId: pane.id,
                    bytes: replayBytes,
                    cloud: !!session.scope.prefix,
                  });
                  skipReplayRemaining = replayBytes;
                }
                return;
              }
              if (skipRestoreReplay) skipNextRestoreReplay = false;
              if (hasOffset) {
                ringOffset = msg.offset!;
                ringEpoch = msg.epoch!;
              }
              const replace = replaceReplay || forceReplace;
              if (replace && replayBytes === 0) {
                // Empty full replay on a reconnect we asked to replace: the
                // daemon's ring has nothing for us yet (fresh post-restart
                // ring whose agent reattach-replay hasn't landed). Our
                // surface belongs to the OLD ring epoch, and the bytes about
                // to fan out are a from-scratch history replay — applied
                // onto the stale surface they jumble (cursor-diff frames
                // against cells that aren't there). Reset now so the
                // incoming stream paints a clean grid, like a first attach.
                // xterm's write queue is FIFO, so any live bytes queued
                // after this write land post-reset.
                term.write('', () => {
                  if (disposed) return;
                  term.reset();
                  const host = hostRef.current;
                  if (host) applyTerminalTheme(term, host, resolveTerminalTheme(useStore.getState()));
                });
                return;
              }
              if (replayBytes > 0) {
                // Counted-replay accounting for BOTH first attach and
                // reconnect. First attach used to stream replay chunks
                // straight into term.write — fine when the daemon sent
                // one frame, but with chunked replay frames there was no
                // completion signal, so the catch-up veil and the final
                // scroll-to-bottom had nothing to anchor on.
                replayActive = true;
                replayIsResume = false;
                replayResetReady = !replace; // fresh terminal needs no reset
                replayFlushing = false;
                replayRemaining = replayBytes;
                replayChunks = [];
                pendingLiveWrites = [];
                replayStripState = newOscStripState();
                if (replayBytes >= CATCHUP_VEIL_MIN_BYTES) {
                  beginCatchup();
                }
                if (replace) {
                  lifecycleLog('pane.term.reset-for-replay', {
                    paneId: pane.id,
                    bytes: replayBytes,
                  });
                  term.write('', () => {
                    if (disposed) return;
                    term.reset();
                    const host = hostRef.current;
                    if (host) applyTerminalTheme(term, host, resolveTerminalTheme(useStore.getState()));
                    replayResetReady = true;
                    flushReplayIfReady();
                  });
                }
              }
              return;
            }
            if (msg.type === 'ownership' && typeof msg.owned === 'boolean') {
              // owner is the daemon's provenance for owned:false — 'other'
              // (a peer really holds input) vs 'none' (nobody does; daemon
              // restarted or the owner left). Absent on old daemons.
              const ownerState =
                msg.owner === 'you' || msg.owner === 'none' || msg.owner === 'other'
                  ? msg.owner
                  : undefined;
              // The daemon sends the initial ownership frame immediately
              // after subscribe. On a desktop first-open/remount we then
              // auto-send {type:"claim"} from onopen, so that first
              // owned:false is only a handshake race, not a real takeover
              // state. Suppress it until the claim ack arrives; passive
              // clients still surface owned:false normally. Exception: a
              // pending CONDITIONAL claim (adopt-unowned, arbitrated
              // first-open/reconnect) can be denied — a LATER owner:"other"
              // frame IS its ack (a peer holds the pane and its user is
              // present), so fall through to the locked state instead of
              // waiting for an owned:true that will never come. The initial
              // frame itself is never that ack (see sawInitialOwnershipFrame).
              const isInitialFrame = !sawInitialOwnershipFrame;
              sawInitialOwnershipFrame = true;
              if (!msg.owned && autoClaimPending) {
                if (isInitialFrame || !(autoClaimConditional && ownerState === 'other')) return;
              }
              autoClaimPending = false;
              const prevOwned = ownedRef.current; // null until the first frame
              ownedRef.current = msg.owned;
              setPaneOwned(key, msg.owned, ownerState, ownershipToken.current);
              // A peer takeover (or a reclaim) just changed who drives the
              // shared PTY width. A displaced viewer (owned:false) is now
              // rendering the peer's-width bytes into its own grid — the
              // wrap-garble with no self-closing edge. Ask for a width-clamped
              // snapshot so it shows clean immediately, and realign: if we're
              // the on-screen active device the forced resend reclaims our
              // width; if a peer is active it's a harmless daemon no-op. Skip
              // the initial ownership frame (prevOwned null) — nothing drifted.
              if (prevOwned != null && prevOwned !== msg.owned) {
                if (!msg.owned) requestClampedRepaint();
                realign('ownership-change');
              }
              // An UNOWNED pane in front of the user must never require a
              // manual "Take over": adopt it. owner:"none" used to be a dead
              // end — adoption only fired at ws-open when this page context
              // remembered owning the pane (ownedRef), which a bundle-update
              // page reload always forgets. So every release (daemon restart
              // wipes ownership + reload wipes ownedRef) parked every pane
              // behind a lock overlay until the user clicked Take over.
              // Desktop-visible viewers now adopt the moment the daemon says
              // nobody holds the pane — on the initial frame after a passive
              // reconnect AND on the broadcast when a ghost owner is reaped.
              // Conditional (adopt-unowned), so a race between two windows
              // resolves truthfully: the loser's denial ack (owner:"other")
              // settles it into the locked state, no ping-pong. Mobile stays
              // passive — pane switches on a phone must not steal input.
              if (
                ownerState === 'none'
                && !isMobileClient
                && currentVisible()
                && ws.readyState === WebSocket.OPEN
              ) {
                autoClaimPending = true;
                autoClaimConditional = true;
                ws.send(JSON.stringify({ type: 'claim', reason: 'adopt-unowned' }));
              }
              return;
            }
            if (msg.type === 'redraw-ack') {
              debugLog('[solu] redraw-ack', { paneId: pane.id, ...msg });
              return;
            }
          } catch { /* not JSON — treat as PTY text */ }
          writeOrQueueLive(ev.data);
        }
      };
      ws.onclose = (ev) => {
        if (wsRef.current !== ws) return;
        abandonTerminalRetirement(key);
        if (
          (typeof document !== 'undefined' && document.visibilityState === 'hidden')
          || (isDesktopApp && !!session.scope.prefix && recentlyRestoreBackgrounded())
        ) {
          markRestoreBackgrounded('ws-close');
        }
        debugLog('[solu] pane ws closed', {
          paneId: pane.id,
          code: ev.code,
          reason: ev.reason,
          wasClean: ev.wasClean,
          cloud: !!session.scope.prefix,
        });
        lifecycleLog('pane.ws.close', {
          paneId: pane.id,
          code: ev.code,
          reason: ev.reason,
          wasClean: ev.wasClean,
          cloud: !!session.scope.prefix,
          visibility: document.visibilityState,
          focused: typeof document.hasFocus === 'function' ? document.hasFocus() : null,
        });
        unregisterSender(pane.id);
        unregisterClaimer(pane.id);
        unregisterRedrawer(pane.id);
        unregisterRealigner(pane.id);
        // A replay cut short by the close would otherwise leave the
        // catch-up veil waiting on its 6s safety timer.
        endCatchup();
        if (disposed) return;
        // 1005/1006 = abnormal close (server gone or network dropped) — retry.
        // 1000 + "pane exited" server-side: normally a genuine exit (don't
        // retry). BUT switch-mode (and daemon reattach) kill the old agent —
        // firing this exact close — then bring up a NEW agent on the SAME pane
        // id. The optimistic body-swap can connect mid-switch and catch the
        // kill. Distinguish via the store: a RESPAWN leaves the pane present and
        // status 'running'; a real exit drops it from the store (or marks it
        // exited). On a respawn, fall through to the reconnect loop (the
        // respawn-reconnect effect also nudges it once the new agent is up) and
        // DON'T paint the scary "[session exited]" / Session-closed overlay.
        let exitedCloseStaleRunning = false;
        if (ev.code === 1000 && ev.reason === 'pane exited') {
          const live = session.pane;
          // A renderer mode switch (Terminal↔Focus) KILLS + RESPAWNS the agent,
          // firing this exact "pane exited" close for the dying agent before the
          // new one comes up on the SAME pane id. During that window
          // paneModeSwitching[pane.id] is true — so NEVER paint the scary
          // "[session exited]" line (it would flash in the terminal for the whole
          // respawn). Fall through to the reconnect loop, which adopts the new
          // agent (the optimistic kind-swap already kept the body visible). The
          // status==='running' check below catches the same respawn for daemons/
          // races where the flag has already cleared; the flag catches the common
          // case where the switch POST hasn't returned yet.
          const switching = !!useStore.getState().paneModeSwitching[pane.id];
          if (!switching && (!live || live.status !== 'running')) {
            setConnStatus('closed');
            term.writeln('\r\n\x1b[90m[session exited]\x1b[0m');
            return;
          }
          // A switch-mode RESPAWN in flight: skip BOTH the "[session exited]" paint
          // (above) AND the exit-settle gate (below). The agent is being
          // kill+respawned on the same pane id; we want a plain, quiet reconnect to
          // adopt the new agent (the respawn-reconnect effect also nudges it),
          // never a settle-to-closed — which could prematurely show the
          // Session-closed overlay if the reconnect timer fires before the new
          // agent's 'running' status lands. The optimistic kind-swap keeps the body
          // visible meanwhile, so the switch reads as an in-place re-render.
          if (!switching) {
            // Store still says 'running', but a non-switch close here has two very
            // different causes: a daemon-reattach RESPAWN body-swap (reconnect to
            // adopt the new agent on the same pane id) OR a genuine natural exit
            // whose 'exited' status hasn't reached the 3s refreshPanes poll yet.
            // Pane-exit is NOT pushed over SSE — only the poll flips .status — so
            // without a nudge the client keeps reconnecting + re-replaying the ring
            // for up to 3s (the visible "flash" on session exit) and the
            // Resume/Close overlay (which needs status==='exited') is delayed. Force
            // an authoritative refresh now and gate the reconnect below on it: a
            // dead pane settles to 'closed' instead of reconnecting; a respawn keeps
            // status 'running' and reconnects as before.
            exitedCloseStaleRunning = true;
            void useStore.getState().refreshPanes();
          }
        }
        setConnStatus('reconnecting');
        // Don't retry while the daemon is mid-self-update — the
        // router will return 502s for ~1-2s, and tight-looping
        // reconnects floods the console + sets connStatus='reconnecting'
        // on every pane simultaneously, making the UI look broken.
        // The applyUpdate flow re-mounts panes via bootstrap() once
        // the daemon is back, so reconnect picks up automatically.
        if (useStore.getState().updateStatus?.applying) {
          heldForUpdateReconnect = true;
          return;
        }
        if (shouldHoldCloudRestoreReconnect()) {
          pendingRestoreReconnect = true;
          lifecycleLog('pane.ws.hold-restore-reconnect', {
            paneId: pane.id,
            visibility: document.visibilityState,
            focused: typeof document.hasFocus === 'function' ? document.hasFocus() : null,
          });
          debugLog('[solu] cloud restore reconnect held until focus', {
            paneId: pane.id,
            visibility: typeof document === 'undefined' ? 'unknown' : document.visibilityState,
            focused: typeof document !== 'undefined' && typeof document.hasFocus === 'function'
              ? document.hasFocus()
              : null,
          });
          return;
        }
        // Exponential backoff: 500ms, 1s, 2s, 4s, capped at 5s.
        const delay = Math.min(500 * 2 ** reconnectAttempt, 5000);
        reconnectAttempt++;
        reconnectTimer = window.setTimeout(() => {
          // If the refresh kicked above (or the periodic poll) has since
          // revealed the pane exited/gone, this was a real session end, not a
          // respawn — don't reopen a socket to a dead pane (the reconnect's
          // ring replay is exactly the flash we're avoiding). Settle to
          // 'closed' so the Session-closed overlay with Resume/Close shows.
          if (exitedCloseStaleRunning) {
            const cur = session.pane;
            if (!cur || cur.status !== 'running') {
              setConnStatus('closed');
              return;
            }
          }
          connect();
        }, delay);
      };
      ws.onerror = () => {
        // onclose will fire next; handled there.
      };
    };
    const unsubscribeUpdateHold = useStore.subscribe((state, prevState) => {
      // Release the reconnect hold once the daemon has stopped applying an
      // update.
      const wasHeld = prevState.updateStatus?.applying === true;
      const isHeld = state.updateStatus?.applying === true;
      if (!wasHeld || isHeld || !heldForUpdateReconnect || disposed) return;
      const ws = wsRef.current;
      if (ws && ws.readyState !== WebSocket.CLOSED) return;
      heldForUpdateReconnect = false;
      connect();
    });
    // Expose connect() to the respawn-reconnect backstop (below).
    connectRef.current = connect;
    connect();

    // Codex resize repair. Used to close the WS (code 4000) to force a
    // fresh subscribe + full ring replay + term.reset — the single
    // biggest visible redraw of all, fired by an ordinary splitter drag.
    // The daemon now exposes {type:"repaint"}: a CUP-addressed full
    // paint from its replay emulator, sent over the LIVE socket. Same
    // ghost-cell repair, no reconnect, no replay, no reset — cheap
    // enough to allow in cloud mode too.
    const scheduleReplayRefreshAfterResize = () => {
      if (resizeRefreshTimer !== null) window.clearTimeout(resizeRefreshTimer);
      resizeRefreshTimer = window.setTimeout(() => {
        resizeRefreshTimer = null;
        const ws = wsRef.current;
        if (disposed || !currentVisible() || !ws || ws.readyState !== WebSocket.OPEN) return;
        debugLog('[solu] codex resize repair via repaint', { paneId: pane.id });
        ws.send(JSON.stringify({ type: 'repaint' }));
      }, 300);
    };

    // Typing claims the shared PTY width. The sizing election only hears
    // arrival events (foreground transition, window refocus, widen, Realign) —
    // steady-state typing in an always-visible window is invisible to it, so
    // with two monitors a grid tile in the other window can hold the pane
    // narrow for hours while the user works here, and every line Claude
    // prints bakes into scrollback at the wrong width. Real input is the
    // strongest attention signal there is; re-stamp on it, throttled.
    // ESC-prefixed data never claims: xterm's onData also carries terminal
    // auto-replies (DA / CPR — idle panes emit these whenever the TUI asks)
    // plus focus/mouse reports, and a background tile claiming width on an
    // auto-reply would recreate the exact bug this fixes. The cost is that
    // arrow-key-only navigation doesn't claim — fine, Enter does.
    let lastTypingClaimAt = 0;
    const TYPING_CLAIM_THROTTLE_MS = 3000;
    const claimSizingOnTyping = (data: string) => {
      if (data.startsWith('\x1b')) return;
      const now = Date.now();
      if (now - lastTypingClaimAt < TYPING_CLAIM_THROTTLE_MS) return;
      lastTypingClaimAt = now;
      sendActiveSizing();
    };

    // Forward keystrokes as raw bytes (binary) so all escape sequences pass through.
    // Drop keystrokes silently if we're not the owner — the UI shows
    // a "Take over" overlay in that state. The server also drops
    // non-owner writes as a second line of defence.
    const dataDisposable = term.onData((data) => {
      if (ownedRef.current === false || !canAct()) return;
      // Mobile: never forward xterm's focus-report bytes. Claude arms DECSET
      // 1004 (focus reporting), and the hidden helper textarea bounces focus
      // constantly on a phone (soft-keyboard show/hide, visualViewport pans,
      // taps) — each bounce makes xterm inject ESC[I/ESC[O into the PTY.
      // Harmless while Claude is foreground (it consumes them) but literal
      // gibberish at any non-1004 child (pager, $EDITOR, shell): ESC[I parses
      // as cursor-forward-tab, so input jumps to a tab stop ("x      y"). They
      // also trigger redundant full redraws (flash). A phone has no meaningful
      // focus/blur to relay, so dropping is lossless. Desktop is untouched.
      if (isMobileViewport() && (data === '\x1b[I' || data === '\x1b[O')) return;
      // A replayed query's answer (vim's mode queries, a cursor report…)
      // would land in whatever is in front now, usually a shell, as text.
      if (replayAnswersRef.current.drops(data)) return;
      const ws = wsRef.current;
      if (ws && ws.readyState === WebSocket.OPEN) {
        // Debug log (enable with `localStorage.setItem('solu.debug','1')`).
        // Paired with the sendToFocused log so we can see whether a
        // duplicated digit is coming from xterm OR the keybar OR both.
        debugLog('[solu] xterm.onData ->', JSON.stringify(data), 'pane=', pane.id);
        // IME trace: what xterm actually emitted (the mangled blob, on mobile).
        // No-op unless ?imetrace=1. Correlated with the composition events below.
        recordIme({ t: performance.now(), kind: 'onData', sent: data });
        resumeFollowIfNearBottom();
        // Dictation's polish checks this so it never rewrites typed input.
        notePaneTyped(pane.id);
        ws.send(encoder.encode(data));
        claimSizingOnTyping(data);
      }
    });

    // Mobile IME instrumentation (LOG-ONLY — no behavior change). xterm's
    // helper-textarea diff mishandles Android predictive REWRITES → the
    // gibberish/misplaced-words bug. The real fix is device-specific and
    // subtle (compositionend.data is documented-unreliable on Chromium; some
    // commits arrive via input/insertText with NO compositionend), so per the
    // project's "data before speculative fixes" rule we capture the REAL
    // Gboard/IME event sequence on a physical device FIRST, then write the
    // precise committer. Enable with localStorage.setItem('solu.debug','1').
    // Pure observers, attached only on phone width.
    let compositionLease: (() => void) | null = null;
    const trackCompositionStart = () => { compositionLease ??= beginTerminalInteraction(key); };
    const trackCompositionEnd = () => { compositionLease?.(); compositionLease = null; };
    term.textarea?.addEventListener('compositionstart', trackCompositionStart);
    term.textarea?.addEventListener('compositionend', trackCompositionEnd);
    let teardownComposition: (() => void) | null = null;
    if (isPhoneWidth && term.textarea) {
      const ta = term.textarea;
      const onCompositionStart = (e: CompositionEvent) => {
        debugLog('[solu] composition start', { paneId: pane.id, data: e.data });
        recordIme({ t: performance.now(), kind: 'c-start', data: e.data });
      };
      const onCompositionUpdate = (e: CompositionEvent) => {
        debugLog('[solu] composition update', { paneId: pane.id, data: e.data });
        recordIme({ t: performance.now(), kind: 'c-update', data: e.data });
      };
      const onCompositionEnd = (e: CompositionEvent) => {
        const taValue = (e.target as HTMLTextAreaElement | null)?.value;
        debugLog('[solu] composition end', { paneId: pane.id, data: e.data, taValue });
        recordIme({ t: performance.now(), kind: 'c-end', data: e.data, taValue });
      };
      const onBeforeInput = (e: InputEvent) => {
        debugLog('[solu] beforeinput', {
          paneId: pane.id,
          inputType: e.inputType,
          data: e.data,
          isComposing: e.isComposing,
        });
        recordIme({
          t: performance.now(),
          kind: 'beforeinput',
          data: e.data,
          inputType: e.inputType,
          isComposing: e.isComposing,
        });
      };
      ta.addEventListener('compositionstart', onCompositionStart);
      ta.addEventListener('compositionupdate', onCompositionUpdate);
      ta.addEventListener('compositionend', onCompositionEnd);
      ta.addEventListener('beforeinput', onBeforeInput as EventListener);
      teardownComposition = () => {
        ta.removeEventListener('compositionstart', onCompositionStart);
        ta.removeEventListener('compositionupdate', onCompositionUpdate);
        ta.removeEventListener('compositionend', onCompositionEnd);
        ta.removeEventListener('beforeinput', onBeforeInput as EventListener);
      };
    }

    const cleanupImagePaste = attachPaneImagePasteHandlers({
      hostEl: hostRef.current,
      paneId: pane.id, scope:session.scope, captureGuard:()=>captureSessionGesture(session),
      beginInteraction: () => beginTerminalInteraction(key),
      wsRef,
      ownedRef,
      encoder,
      // Muse gets the plain path: `@`-mentions are Claude syntax and the
      // Muse TUI fails attaching them. Everything else keeps `@`.
      atMention: !isMusePane,
    });

    // Mouse copy/paste parity (issue #16) — the X11 primary-selection
    // convention that wezterm, gnome-terminal, konsole, kitty and
    // Alacritty all ship: copy-on-select + middle-click paste. Both
    // toggles are read live from the store so flipping them in
    // Preferences takes effect without remounting the pane. Middle-click
    // rides xterm's paste path, so CRLF and bracketed paste behave like
    // a normal paste (issue #6).
    const cleanupMouseParity = attachPaneMousePasteHandlers({
      hostEl: hostRef.current,
      term,
      ownedRef,
      canAct,
      beginInteraction: () => beginTerminalInteraction(key),
      captureGuard: () => captureSessionGesture(session),
      copy: copyToClipboard,
    });
    // Resize handling — observe the host element.
    //
    // We deliberately go through the WebSocket `resize` frame ONLY,
    // NOT via api.resizePane(). The HTTP endpoint calls p.Resize()
    // directly and bypasses the sub-aware recomputeSize() — so a PC
    // client's resize would reset the PTY to PC cols even when a
    // phone (force + visible) should be winning. The WS path updates
    // this sub's cols, runs recomputeSize, and only resizes the PTY
    // if the resolved dims actually change.
    // On mobile, skip row-only changes. Virtual keyboard opening
    // shrinks viewport HEIGHT (not width) → new rows → resize sent
    // → Claude SIGWINCH → full UI redraw. User sees that as a
    // distracting scroll-refresh every time they tap to type.
    // Width changes (rotation, real layout shifts) still go through.
    let lastSentCols = term.cols;
    let lastSentRows = term.rows;
    // Drag detection via ResizeObserver cadence. Tauri's WebView doesn't
    // reliably fire pointerdown on react-resizable-panels handles (the
    // diag trace showed zero pointerdown events for actual drags), so we
    // can't anchor on user input events. Instead: treat ANY RO fire as
    // "drag might be in progress", and clear 200ms after the last fire.
    // While flagged, the fit wrapper skips its own snapshot() and keeps
    // using the last clean preDragRef — that's the baseline from the
    // user's last explicit interaction (wheel/key/mount), not the
    // mid-drag drifted state. Claude writes during the drag don't corrupt
    // the snapshot either, because the write listener (below) also skips
    // while draggingRef.current is true.
    let dragEndTimer: number | null = null;
    let pendingResizeTimer: number | null = null;
    let pendingResizeForce = false;
    // Debounced PTY-resize sender. fit() still runs on every RO tick
    // (keeps xterm's local cell grid aligned with the container
    // during drag so the UI doesn't lag), but the WS resize frame —
    // which becomes a SIGWINCH on the running TUI — is held back
    // until the drag settles. Without the debounce, a 300 ms
    // splitter drag fires 15–30 WS resizes. Each becomes a SIGWINCH
    // on codex, overwhelming Ratatui's per-draw-tick autoresize and
    // producing partial / interleaved frames (symptom: "empty lines
    // accumulate in plain shell" / "duplicate input row in codex").
    //
    // Earlier revisions also sent a (cols-1, cols) size-bump here
    // to "force" a full repaint. That backfired: Ratatui's
    // autoresize coalesces SIGWINCHes that arrive between draw
    // ticks into a single resize event, and the coalesced event
    // emits a partial frame covering only the newly-grown edges —
    // leaving cells in the old area ghost'd against the daemon's
    // clear-inject (v0.0.172). A single deliberate resize doesn't
    // hit this trap. Removed; we rely on the daemon-side clear-
    // inject (pane.go Resize when altScreen) for ghost-cell
    // prevention, not on forcing multiple SIGWINCHes.
    const schedulePTYResize = (force = false) => {
      // A ResizeObserver tick must not erase a forced restore/font resend
      // queued in the same burst, even when local dimensions are unchanged.
      pendingResizeForce ||= force;
      if (pendingResizeTimer !== null) window.clearTimeout(pendingResizeTimer);
      pendingResizeTimer = window.setTimeout(() => {
        pendingResizeTimer = null;
        const forceResize = pendingResizeForce;
        pendingResizeForce = false;
        if (disposed || !readUsableHostRect('pty-resize-send')) return;
        const ws = wsRef.current;
        if (!ws || ws.readyState !== WebSocket.OPEN) return;
        const colsChanged = term.cols !== lastSentCols;
        const rowsChanged = term.rows !== lastSentRows;
        const prevCols = lastSentCols;
        const prevRows = lastSentRows;
        const rowDelta = Math.abs(term.rows - prevRows);
        // force=true RE-ASSERTS our measured width even when OUR cols/rows
        // didn't change, bypassing the no-op + jitter guards below. It is the
        // fix for garble whose cause is a change to the SHARED PTY width from
        // ANOTHER source — a peer takeover, a post-shutdown resume, an app-
        // update reattach — with no local pixel change, so the ResizeObserver
        // never fires and this guard would otherwise swallow the corrective
        // resend. The daemon dedups an unchanged resolved size, so a realign
        // that already matches reality is a cheap no-op; only a real mismatch
        // triggers a SIGWINCH. This is the Alt+B round-trip minus the resize.
        if (!forceResize) {
          // Alt-screen (Claude) keeps the grid stable when the virtual keyboard
          // changes height (the host is translated, not resized). Normal-buffer
          // (Codex) DOES resize-to-fit above the keyboard, so its row-only
          // changes must reach the PTY — fall through to the small-jitter guard
          // below, which still ignores ≤2-row chrome wobble.
          if (isPhoneWidth && !colsChanged && rowsChanged && !hasCodexRef.current) return;
          if (!colsChanged && !rowsChanged) return;
          if (hasCodexRef.current && !colsChanged && rowDelta <= 2) {
            // Last-prompt and other one-line chrome changes should not
            // SIGWINCH Codex. That redraw/reflow is the fragile part that
            // makes a harmless UI row feel like the terminal jumped upward.
            return;
          }
        }
        lastSentCols = term.cols;
        lastSentRows = term.rows;
        ws.send(JSON.stringify({ type: 'resize', cols: term.cols, rows: term.rows }));
        const colDelta = Math.abs(term.cols - prevCols);
        const resizeRepairSuppressed = Date.now() < suppressResizeRepairUntil;
        // A late forced restore fit can change one row after the first paint
        // already ran. Repair that final grid too: suppression and the normal
        // jitter threshold must not leave the footer in the discarded row.
        const restoreGeometryChanged = forceResize && (colsChanged || rowsChanged);
        if (hasCodexRef.current && (restoreRepaintPending || restoreGeometryChanged || ((colDelta >= 8 || rowDelta >= 3) && !resizeRepairSuppressed))) {
          restoreRepaintPending = false;
          scheduleReplayRefreshAfterResize();
        } else if (resizeRefreshTimer !== null) {
          // A later settle pass postpones repair until the final geometry.
          scheduleReplayRefreshAfterResize();
        }
      }, 100);
    };
    const restoreRefitTimers: number[] = [];
    let restoreRefitRafOuter = 0;
    let restoreRefitRafInner = 0;
    // While set in the future, every refit pass re-pins the viewport to
    // the bottom BEFORE it snapshots — so snapshot() records wasAtBottom
    // and fitPreservingScroll preserves bottom instead of restoring the
    // stale (parked) position. Set on warm-pane reattach (workspace
    // switch-back); the user's chosen policy is "always jump to latest".
    let forceBottomUntil = 0;
    const clearRestoreRefitTimers = () => {
      while (restoreRefitTimers.length > 0) {
        const id = restoreRefitTimers.pop();
        if (id !== undefined) window.clearTimeout(id);
      }
      if (restoreRefitRafOuter) {
        window.cancelAnimationFrame(restoreRefitRafOuter);
        restoreRefitRafOuter = 0;
      }
      if (restoreRefitRafInner) {
        window.cancelAnimationFrame(restoreRefitRafInner);
        restoreRefitRafInner = 0;
      }
    };
    const runRestoreRefitPass = (source: string, force = false) => {
      if (disposed || !currentVisible()) return;
      if (Date.now() < forceBottomUntil) {
        try { term.scrollToBottom(); } catch { /* best-effort */ }
      }
      const before = { cols: term.cols, rows: term.rows };
      if (!readUsableHostRect(source)) return;
      try {
        if (!draggingRef.current) snapshot();
        if (!fitPreservingScroll()) return;
        try {
          term.refresh(0, Math.max(0, term.rows - 1));
        } catch { /* renderer may already be disposed */ }
        lifecycleLog('pane.restore-refit-pass', {
          paneId: pane.id,
          source,
          before,
          after: { cols: term.cols, rows: term.rows },
          visibility: typeof document === 'undefined' ? 'unknown' : document.visibilityState,
          focused: typeof document !== 'undefined' && typeof document.hasFocus === 'function'
            ? document.hasFocus()
            : null,
        });
        schedulePTYResize(force);
      } catch (err) {
        lifecycleLog('pane.restore-refit-error', {
          paneId: pane.id,
          source,
          error: err instanceof Error ? err.message : String(err),
        });
      }
    };
    const scheduleRestoreRefit = (source: string, force = false) => {
      if (disposed || !currentVisible()) return;
      // Avoid treating restore-settle fits like an intentional splitter
      // drag that needs a replay reconnect. We still send a normal resize
      // if cols/rows changed; only the expensive local replay repair is
      // suppressed during this short window.
      clearRestoreRefitTimers();
      suppressResizeRepairUntil = Date.now() + 2000;
      lifecycleLog('pane.restore-refit-scheduled', {
        paneId: pane.id,
        source,
        cols: term.cols,
        rows: term.rows,
        lastGoodFit,
        visibility: typeof document === 'undefined' ? 'unknown' : document.visibilityState,
      });
      restoreRefitRafOuter = window.requestAnimationFrame(() => {
        restoreRefitRafOuter = 0;
        restoreRefitRafInner = window.requestAnimationFrame(() => {
          restoreRefitRafInner = 0;
          runRestoreRefitPass(`${source}:raf2`, force);
        });
      });
      for (const delay of [50, 250, 750]) {
        restoreRefitTimers.push(window.setTimeout(() => runRestoreRefitPass(`${source}:${delay}ms`, force), delay));
      }
    };
    // realign — the self-heal for shared-PTY width drift (peer takeover, post-
    // shutdown resume, app-update reattach). FORCE-resends our measured width so
    // that if this device already drives the pane's sizing (most-recently-active
    // visible sub), the daemon resizes the PTY back to our width and the TUI
    // repaints aligned — no manual Alt+B. It deliberately does NOT re-stamp
    // active sizing: a plain resend can only WIN the election, never steal it,
    // so a background/passive view (a pocketed phone still counted "visible")
    // can't yank the width from the device the user is actually on. Callers that
    // SHOULD grab sizing (the user's own Realign button) send {type:'active'}
    // themselves; reconnect/visibility already re-stamp active via their own
    // (guarded) paths. The restore pass's readUsableHostRect gate keeps a truly
    // hidden pane from resending at all.
    const realign = (source: string) => {
      if (disposed) return;
      scheduleRestoreRefit(source, /* force */ true);
    };
    fontRefitRef.current = () => {
      // Font settings reach parked warm panes too. Apply their options now,
      // but measure and report geometry only once their host is visible.
      if (!currentVisible()) return;
      restoreRepaintPending = hasCodexRef.current;
      realign('font-change');
    };
    // requestClampedRepaint — ask the daemon for a width-clamped grid snapshot
    // (RepaintGridFor) over the live socket, so a DISPLACED viewer whose width
    // no longer matches the PTY shows a clean (if edge-truncated) frame instead
    // of wrap-garble until it reclaims sizing. No reconnect, no replay, no reset.
    const requestClampedRepaint = () => {
      const ws = wsRef.current;
      if (ws && ws.readyState === WebSocket.OPEN && currentVisible()) {
        ws.send(JSON.stringify({ type: 'repaint' }));
      }
    };
    const ro = new ResizeObserver(() => {
      if (typeof document !== 'undefined' && document.visibilityState === 'hidden') {
        suppressResizeRepairUntil = Date.now() + 1500;
        return;
      }
      if (!readUsableHostRect('resize-observer')) return;
      // Ordinary UI chrome changes also resize the xterm host: approval
      // strips appear/disappear, update banners mount, memo rows open,
      // and font/layout settles. Those are not splitter drags; restoring
      // from an old preDragRef makes Codex jump upward to a stale line.
      //
      // Take one fresh live snapshot at the start of every resize burst.
      // For real splitter drags, subsequent RO ticks keep using that burst
      // baseline until the resize quiets, preserving the existing anti-drift
      // behavior. For one-off UI resizes, the baseline is simply the current
      // viewport, so bottom-follow stays bottom-follow.
      if (!draggingRef.current) {
        snapshot();
      }
      draggingRef.current = true;
      if (dragEndTimer !== null) window.clearTimeout(dragEndTimer);
      dragEndTimer = window.setTimeout(() => {
        draggingRef.current = false;
        dragEndTimer = null;
      }, 200);
      try {
        fitPreservingScroll();
        schedulePTYResize();
      } catch {}
    });
    ro.observe(hostRef.current);

    // Visibility-aware sizing: tell the daemon when this tab goes to
    // background / returns to foreground, so backgrounded clients
    // don't dictate PTY size. See subEntry.visible in daemon/pane.go.
    const onVisibility = () => {
      suppressResizeRepairUntil = Date.now() + 1500;
      if (typeof document !== 'undefined' && document.visibilityState === 'hidden') {
        detachInputHandlers();ro.disconnect();
        markRestoreBackgrounded('visibility-hidden');
      }
      if(canAct()){attachInputHandlers();if(hostRef.current)ro.observe(hostRef.current);}
      const ws = wsRef.current;
      if (currentVisible() && ws?.readyState === WebSocket.OPEN) {
        nudgeRestorePaint();
        // Forced: tabbing back can leave the shared PTY at a width a peer/restart
        // drove while we were hidden, with no local pixel change to fire the RO.
        realign('visibility-visible');
        const restoreWs = ws;
        window.setTimeout(() => {
          if (
            !disposed
            && document.visibilityState === 'visible'
            && wsRef.current === restoreWs
            && restoreWs.readyState === WebSocket.OPEN
          ) {
            skipNextRestoreReplay = false;
            lastRestoreBackgroundAt = 0;
          }
        }, 1500);
      }
      if (
        typeof document !== 'undefined'
        && document.visibilityState === 'visible'
        && pendingRestoreReconnect
        && (!ws || ws.readyState === WebSocket.CLOSED)
      ) {
        connect();
        return;
      }
      if (!ws || ws.readyState !== WebSocket.OPEN) return;
      ws.send(
        JSON.stringify({
          type: 'visibility',
          visible: currentVisible(),
        }),
      );
    };
    document.addEventListener('visibilitychange', onVisibility);
    const onWindowBlur = () => {
      // In desktop cloud mode, minimizing the Tauri window may not
      // transition document.visibilityState to "hidden", but the
      // cloud WebSocket can still close while the WebView is backgrounded.
      if (isDesktopApp && session.scope.prefix) markRestoreBackgrounded('window-blur');
    };
    const onDesktopWillBackground = (event: Event) => {
      detachInputHandlers();ro.disconnect();sendVisibilityNow();
      if (!isDesktopApp || !session.scope.prefix) return;
      const reason = (event as CustomEvent<{ reason?: string }>).detail?.reason;
      markRestoreBackgrounded(reason ? `desktop-${reason}` : 'desktop-will-background');
    };
    const onWindowFocus = () => {
      if (pendingRestoreReconnect) {
        connect();
        scheduleRestoreRefit('window-focus-reconnect');
        return;
      }
      const ws = wsRef.current;
      if (ws?.readyState === WebSocket.OPEN && isRestoreBackgrounded()) {
        nudgeRestorePaint();
        realign('window-focus-restore');
      }
      // The window the user just focused should own the shared PTY width for
      // the pane they're looking at — reclaim sizing for the focused, on-screen
      // pane so it overtakes a background-tile / stale sub in another window.
      if (canAct() && effectiveTerminalTarget(useStore.getState()) === pane.id) {
        sendActiveSizing();
      }
    };
    const onDesktopRestored = (event: Event) => {
      setPlacementEpoch((value) => value + 1);
      if(canAct()){attachInputHandlers();if(hostRef.current)ro.observe(hostRef.current);}
      sendVisibilityNow();
      const reason = (event as CustomEvent<{ reason?: string }>).detail?.reason;
      scheduleRestoreRefit(reason ? `desktop-${reason}` : 'desktop-restored');
    };
    // Warm pane brought back on-screen (workspace switch-back). The host
    // moved from the hidden parking lot into a visible slot; xterm's
    // auto-refresh-on-visible isn't firing reliably, leaving stale cells
    // and a viewport stranded above the latest output (live bytes that
    // streamed in while parked register as "N new lines"). Force a canvas
    // repaint, re-fit for the now-visible size, and pin to the bottom.
    const onPaneReattach = (event: Event) => {
      if ((event as CustomEvent<{ paneId?: string }>).detail?.paneId !== key && (event as CustomEvent<{sessionKey?:string}>).detail?.sessionKey !== key) return;
      setPlacementEpoch((value) => value + 1);
      // Back on-screen: report visible:true so this view rejoins the sizing
      // election (the daemon's hidden→visible transition also re-stamps it
      // active, so a workspace switch-back reclaims the PTY width).
      onScreen = true;
      attachInputHandlers();
      sendVisibilityNow();
      // Refreshing the renderer alone cannot repair stale Codex buffer cells.
      // Request one authoritative screen paint after the settled resize, even
      // if our local dimensions stayed the same while another viewer had it.
      restoreRepaintPending = hasCodexRef.current;
      // Owner/workspace return preserves the retained viewport and draft.
      forceBottomUntil = session.retained ? 0 : Date.now()+1000;
      if(!session.retained) {try {term.scrollToBottom();}catch{/* existing ordinary restore policy */}}
      if (hostRef.current) ro.observe(hostRef.current);
      nudgeRestorePaint();
      // Forced: a workspace switch-back re-parents the host without a pixel-size
      // change; sendVisibilityNow above re-stamps active, so this reclaims width.
      realign('warm-pane-reattach');
    };
    // Parked off-screen (workspace switch-away / window backgrounded): drop out
    // of the sizing election so a background tile can't pin an active pane.
    const onPanePark = (event: Event) => {
      if ((event as CustomEvent<{ paneId?: string }>).detail?.paneId !== key && (event as CustomEvent<{sessionKey?:string}>).detail?.sessionKey !== key) return;
      setPlacementEpoch((value) => value + 1);
      onScreen = false;
      if(catchupSafetyTimer !== null)window.clearTimeout(catchupSafetyTimer);
      if(catchupFadeTimer !== null)window.clearTimeout(catchupFadeTimer);
      catchupSafetyTimer=null;catchupFadeTimer=null;setCatchup(null);
      detachInputHandlers();
      if(writeParsedSnapshotRaf)cancelAnimationFrame(writeParsedSnapshotRaf);
      if(writeParsedSnapshotInnerRaf)cancelAnimationFrame(writeParsedSnapshotInnerRaf);
      writeParsedSnapshotRaf=0;writeParsedSnapshotInnerRaf=0;
      ro.disconnect();
      clearRestoreRefitTimers();
      if (pendingResizeTimer !== null) window.clearTimeout(pendingResizeTimer);
      pendingResizeTimer = null;
      pendingResizeForce = false;
      if (resizeRefreshTimer !== null) window.clearTimeout(resizeRefreshTimer);
      resizeRefreshTimer = null;
      restoreRepaintPending = false;
      if (dragEndTimer !== null) window.clearTimeout(dragEndTimer);
      dragEndTimer = null;
      draggingRef.current = false;
      forceBottomUntil = 0;
      sendVisibilityNow();
    };
    window.addEventListener('blur', onWindowBlur);
    window.addEventListener('solu:desktop-will-background', onDesktopWillBackground as EventListener);
    window.addEventListener('solu:desktop-restored', onDesktopRestored as EventListener);
    window.addEventListener('solu:pane-reattach', onPaneReattach as EventListener);
    window.addEventListener('solu:pane-park', onPanePark as EventListener);
    window.addEventListener('focus', onWindowFocus);

    // App-level keepalive: bump the daemon's per-sub liveness (lastSeenAt) so an
    // idle-but-connected viewer over the cloud relay — where WS ping/pong is
    // stripped by the tunnel — isn't treated as stale by desiredSizeLocked and
    // dropped from the sizing election.
    const unregisterKeepalive = registerSessionKeepalive(key, () => {
      const ws = wsRef.current;
      if (ws && ws.readyState === WebSocket.OPEN) {
        ws.send(JSON.stringify({ type: 'ping' }));
      }
    });

    return () => {
      lifecycleLog('pane.unmount', {
        paneId: pane.id,
        backend: pane.backend,
        prefix: session.scope.prefix,
        visibility: document.visibilityState,
      });
      cleanCloseViewer();
      unregisterCleanClose();
      window.removeEventListener('pagehide', onRetirementPageHide, { capture: true });
      disposed = true;
      replayAnswersRef.current.reset();
      abandonTerminalRetirement(key);
      trackCompositionEnd();
      term.textarea?.removeEventListener('compositionstart', trackCompositionStart);
      term.textarea?.removeEventListener('compositionend', trackCompositionEnd);
      fontRefitRef.current = null;
      document.removeEventListener('visibilitychange', onVisibility);
      window.removeEventListener('blur', onWindowBlur);
      window.removeEventListener('solu:desktop-will-background', onDesktopWillBackground as EventListener);
      window.removeEventListener('solu:desktop-restored', onDesktopRestored as EventListener);
      window.removeEventListener('solu:pane-reattach', onPaneReattach as EventListener);
      window.removeEventListener('solu:pane-park', onPanePark as EventListener);
      window.removeEventListener('focus', onWindowFocus);
      unregisterKeepalive();
      detachInputHandlers();
      document.removeEventListener('pointerdown', onGlobalPointerDown, true);
      document.removeEventListener('mousedown', onGlobalPointerDown as EventListener, true);
      document.removeEventListener('pointerup', onGlobalPointerUp, true);
      document.removeEventListener('mouseup', onGlobalPointerUp, true);
      document.removeEventListener('pointercancel', onGlobalPointerUp, true);
      hostElForSnapshot?.removeEventListener('wheel', deferredMaybeSnapshot);
      hostElForSnapshot?.removeEventListener('keydown', deferredMaybeSnapshot);
      hostElForSnapshot?.removeEventListener('pointerdown', cancelRestoreOnPointer, true);
      writeParsedSnapshotDisp.dispose();
      if (writeParsedSnapshotRaf) cancelAnimationFrame(writeParsedSnapshotRaf);
      if (writeParsedSnapshotInnerRaf) cancelAnimationFrame(writeParsedSnapshotInnerRaf);
      if (rebaselineRafOuter) cancelAnimationFrame(rebaselineRafOuter);
      if (rebaselineRafInner) cancelAnimationFrame(rebaselineRafInner);
      if (dragEndTimer !== null) window.clearTimeout(dragEndTimer);
      if (pendingResizeTimer !== null) window.clearTimeout(pendingResizeTimer);
      if (resizeRefreshTimer !== null) window.clearTimeout(resizeRefreshTimer);
      if (catchupSafetyTimer !== null) window.clearTimeout(catchupSafetyTimer);
      if (catchupFadeTimer !== null) window.clearTimeout(catchupFadeTimer);
      clearRestoreRefitTimers();
      ro.disconnect();
      dataDisposable.dispose();
      cleanupReaderMode();
      try { bufferChangeDisp.dispose(); } catch { /* already disposed */ }
      try { followAfterReturnDisp.dispose(); } catch { /* already disposed */ }
      unregisterSender(pane.id);
      unregisterPaneSnapshot(pane.id);
      unregisterClaimer(pane.id);
      unregisterRedrawer(pane.id);
      unregisterRealigner(pane.id);
      unsubscribeUpdateHold();
      clearPaneOwnership(key, ownershipToken.current);
      hostRef.current?.removeEventListener('wheel', onWheel, { capture: true });
      removeHealListener?.();
      cleanupImagePaste();
      cleanupMouseParity();
      teardownComposition?.();
      if (reconnectTimer) window.clearTimeout(reconnectTimer);
      try { wsRef.current?.close(); } catch {}
      teardownMobileTouchFix?.();
      if (debugWin.__soluTerms?.get(key) === term) debugWin.__soluTerms.delete(key);
      if (isEmbedded()) window.removeEventListener('solu:embed-visible', onEmbedVisible);
      try { term.dispose(); } catch { /* ignore — final dispose is best effort */ }
      termRef.current = null;
      searchAddonRef.current = null;
      try { findResultsDisp.dispose(); } catch { /* addon already disposed */ }
      try { linkProviderDisp.dispose(); } catch { /* addon already disposed */ }
      try { oscCopyDisp.dispose(); } catch { /* addon already disposed */ }
      try { oscSoluDisp.dispose(); } catch { /* addon already disposed */ }
      clearPaneRunningWork(key);
      wsRef.current = null;
      connectRef.current = null;
    };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [key]);

  // Respawn-reconnect backstop. A switch-mode kill+respawn (or a daemon
  // reattach) brings up a NEW agent on the SAME pane id — its pid changes and
  // status returns to 'running'. The old agent's "pane exited" close may have
  // already settled our WS (the optimistic body-swap connects mid-switch), so
  // when the pane is alive again but we're not connected, re-open the socket to
  // the fresh agent. Keyed off pid so it fires exactly once per respawn; reads
  // connStatus from the render snapshot (not a dep) to avoid reconnect churn.
  useEffect(() => {
    if (pane.status !== 'running') return;
    // Only act when we've actually given up ('closed'); 'reconnecting' already
    // has the backoff loop retrying, and open/connecting need no help.
    if (connStatus !== 'closed') return;
    connectRef.current?.();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [pane.pid, pane.status]);

  // Live theme swaps — re-apply when the user picks a different scheme or
  // Appearance flips (Dark/Light/System, including System-mode OS changes),
  // so existing panes repaint in place without a reload or respawn.
  useEffect(() => {
    const term = termRef.current;
    if (!term) return;
    const host = hostRef.current;
    if (!host) return;
    applyTerminalTheme(term, host, resolveTerminalTheme({
      terminalThemeName,
      terminalThemeExplicit,
      appThemeLight,
    }));
  }, [terminalThemeName, terminalThemeExplicit, appThemeLight]);

  // Live scrollback re-sizing when the visible pane count crosses a
  // threshold (e.g. opening the 5th pane drops every terminal from 20000 →
  // 12000). xterm supports changing scrollback at runtime via term.options;
  // SHRINKING drops the oldest history — the accepted memory/UX tradeoff for
  // large grids. We never grow past 20000. Guarded so we only touch xterm
  // when the computed value actually changes, keeping this off the hot path.
  useEffect(() => {
    const term = termRef.current;
    if (!term) return;
    if (session.retained || pane.role === 'task_owner') return;
    const next = scrollbackForPaneCount(paneCount);
    if (term.options.scrollback !== next) {
      term.options.scrollback = next;
    }
  }, [paneCount]);

  // Live font-size / line-height swaps. Changing either invalidates
  // xterm's cell dimensions, so we refit (which recalculates rows/cols
  // from the container pixel size) and push a PTY resize to match —
  // otherwise the shell keeps wrapping at the old geometry.
  useEffect(() => {
    const term = termRef.current;
    if (!term) return;
    term.options.fontSize = terminalFontSize;
    term.options.lineHeight = terminalLineHeight;
    // Share the guarded, post-paint WebSocket resize path with restores. The
    // HTTP resize endpoint bypasses viewer sizing and can let a hidden pane
    // overwrite the geometry chosen by the device the user is looking at.
    fontRefitRef.current?.();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [terminalFontSize, terminalLineHeight]);

  return (
    <div
      className={`pane ${focused ? 'focused' : ''} ${unread ? 'unread' : ''} ${pane.state || ''} ${beingDragged ? 'dragging' : ''} ${dictating ? 'dictating' : ''} ${revealed ? 'revealed' : ''} ${pane.flagged ? 'flagged' : ''}`}
      // Marker so the spatial-focus keyboard handlers (Alt+H/J/K/L) can
      // look up each pane's on-screen rect by id.
      data-pane-id={pane.id}
      // capture phase so clicks inside xterm still focus the pane, since
      // xterm's own mousedown handler stops propagation.
      onMouseDownCapture={() => {if(canAct()) setFocus(pane.id);}}
      onContextMenu={openContextMenu}
      onDragOver={(e) => {
        // Only engage with our own drag payload.
        if (!e.dataTransfer.types.includes(DRAG_MIME)) return;
        e.preventDefault();
        e.dataTransfer.dropEffect = 'move';
        setDropZone(computeZone(e));
      }}
      onDragLeave={(e) => {
        // Fires when crossing into a child too — only clear when we truly leave.
        const related = e.relatedTarget as Node | null;
        if (!e.currentTarget.contains(related)) setDropZone(null);
      }}
      onDrop={(e) => {
        if (!actionValid() || ownerPresentation || !e.dataTransfer.types.includes(DRAG_MIME)) return;
        e.preventDefault();
        const src = e.dataTransfer.getData(DRAG_MIME);
        const zone = computeZone(e);
        setDropZone(null);
        if (src && src !== pane.id) movePane(src, pane.id, zone);
      }}
    >
      {canAct() && <PaneHeader
        ownerPresentation={ownerPresentation}
        actionGuard={actionValid}
        pane={pane}
        paneIndex={paneIndex}
        activityClass={activityClass}
        editingTitle={editingTitle}
        titleDraft={titleDraft}
        unread={unread}
        unreadKind={unreadKind}
        connStatus={connStatus}
        isZoomed={isZoomed}
        canZoom={canZoom && !ownerPresentation}
        setTitleDraft={setTitleDraft}
        setEditingTitle={setEditingTitle}
        onDragStart={(e) => {
          e.dataTransfer.setData(DRAG_MIME, pane.id);
          e.dataTransfer.effectAllowed = 'move';
          setBeingDragged(true);
        }}
        onDragEnd={() => setBeingDragged(false)}
        onRename={async (title) => {if(actionValid()) await renamePane(pane.id, title);}}
        onClose={() => { if(actionValid()) {void killPane(pane.id);} }}
        onToggleZoom={() => {if(actionValid() && !ownerPresentation) toggleZoom(pane.id);}}
        onSwitchMode={(kind) => { if(actionValid() && !ownerPresentation) void switchPaneMode(pane.id, kind); }}
        onOpenMenu={openContextMenu}
      />}

      {/* Wrap the flag-memo + last-prompt rows so mobile can take them out of
          the flex flow (height:0 overlay) WITHOUT resizing .pane-body — a
          pane-body resize fires the host ResizeObserver -> fit refit -> flash.
          See .pane-chrome-rows in styles.css. Desktop keeps them in-flow. */}
      {canAct() && <div className="pane-chrome-rows">
        <PaneFlagMemo
          actionGuard={actionValid}
          onSave={async(flagged,memo)=>{if(!actionValid())return;const valid=captureSessionGesture(session);if(!valid())return;const changed=await api.setPaneFlag(pane.id,flagged,memo,session.scope);if(valid())applyPaneSnapshot(changed);}}
          pane={pane}
          editing={editingFlagMemo}
          draft={flagMemoDraft}
          setEditing={setEditingFlagMemo}
          setDraft={setFlagMemoDraft}
        />
        <PaneLastPrompt
          prompts={lastPrompts}
          expanded={lastPromptExpanded}
          setExpanded={setLastPromptExpanded}
        />
      </div>}
      {ctxMenu && canAct() && (
        <PaneContextMenu
          managedOwner={pane.role === 'task_owner'}
          pane={pane}
          x={ctxMenu.x}
          y={ctxMenu.y}
          menuRef={ctxMenuRef}
          isClaudePane={isClaudePane}
          onSplitRight={ctxMenuActions.splitRight}
          onSplitRightShellHere={() => {
            if(!actionValid() || ownerPresentation)return;
            closeContextMenu();
            void launchShellHere(pane.id, 'horizontal');
          }}
          onSplitRightClaudeHere={() => {
            if(!actionValid() || ownerPresentation)return;
            closeContextMenu();
            void launchClaudeHere(pane.id, 'horizontal');
          }}
          onSplitDown={ctxMenuActions.splitDown}
          onClonePane={ctxMenuActions.clonePane}
          onMoveToWorkspace={pane.role !== 'task_owner' ? ctxMenuActions.moveToWorkspace : undefined}
          onNewSession={ctxMenuActions.newSession}
          onCreateSchedule={ctxMenuActions.createSchedule}
          onSetAutoMode={ctxMenuActions.setAutoMode}
          onToggleAnnounceDelegation={(isClaudePane || isCodexPane) && operatorFeaturesAllowed() ? ctxMenuActions.toggleAnnounceDelegation : undefined}
          onEditFlagMemo={ctxMenuActions.editFlagMemo}
          onUnflag={ctxMenuActions.unflag}
          onFlagForAttention={ctxMenuActions.flagForAttention}
          onRename={ctxMenuActions.rename}
          onEditIdentity={() => {
            if(!actionValid())return;
            closeContextMenu();
            setIdentityDialogOpen(true);
          }}
          onConvertRole={pane.role !== 'task_owner' && operatorFeaturesAllowed() && roleConvertAllowed(pane, useStore.getState().orchestratorHosts) ? ctxMenuActions.convertRole : undefined}
          onChangeContextPack={() => {
            if(!actionValid())return;
            closeContextMenu();
            setContextPackDialogOpen(true);
          }}
          onDetachContextPack={() => {
            if(!actionValid())return;
            closeContextMenu();
            void setPaneContextPack(pane.id, '');
          }}
          onRedraw={() => {
            if(!actionValid())return;
            closeContextMenu();
            redrawPane(pane.id);
          }}
          onRealign={() => {
            if(!actionValid())return;
            closeContextMenu();
            realignPane(pane.id);
          }}
          onRestartPane={() => {
            closeContextMenu();
            if (actionValid()) void restartPaneFlow(pane.id,{scope:session.scope,valid:captureSessionGesture(session)});
          }}
          onClosePane={ctxMenuActions.closePane}
          selectionText={menuSelection}
          sendTargets={menuSendTargets}
          onSendSelection={(targetId) => {
            if(!actionValid())return;
            const text = menuSelection;
            closeContextMenu();
            if (!text) return;
            const target = menuSendTargets.find((t) => t.id === targetId);
            window.dispatchEvent(new CustomEvent('solu:pane-paste', { detail: { paneId: targetId, pid: target?.pid, text } }));
            void useStore.getState().revealPane(targetId);
          }}
          onSearchSelection={() => {
            if(!actionValid())return;
            const text = menuSelection.replace(/\s+/g, ' ').trim().slice(0, 200);
            closeContextMenu();
            if (!text) return;
            window.dispatchEvent(new CustomEvent('solu:open-palette', { detail: { mode: 'search', query: text } }));
          }}
          onLastTurnDiff={pane.turn?.last ? () => {
            if(!actionValid())return;
            closeContextMenu();
            useStore.getState().openTurnDiff(pane.id);
          } : undefined}
          onReviewChanges={pane.status === 'running' ? () => {
            if(!actionValid())return;
            closeContextMenu();
            useStore.getState().openDiffHere(pane.liveCwd || pane.cwd, false, pane.id);
          } : undefined}
        />
      )}
      {identityDialogOpen && canAct() && (
        <PaneIdentityDialog pane={pane} onClose={() => setIdentityDialogOpen(false)} />
      )}
      {contextPackDialogOpen && canAct() && (
        <ContextPackDialog
          title="Context pack — pane"
          value={pane.contextPack ?? ''}
          onSave={async (dir) => { if(actionValid()) await setPaneContextPack(pane.id, dir); }}
          onClose={() => setContextPackDialogOpen(false)}
        />
      )}
      <div
        className="pane-body"
        ref={hostRef}
        style={{ [TERMINAL_BACKGROUND_CSS_PROPERTY]: terminalBackground } as CSSProperties}
      >
        {retirementPaused && <div className="pane-switching-scrim" role="status" aria-live="polite"><span className="pane-switching-label">Retiring previous owner… Input is briefly paused.</span></div>}
        <PreservedTerminalInput recoveryKey={recoveryKey} overlay valid={() => !session.invalid && session.principal === routingPrincipalEpoch() && routingPrincipalAllowed()} />

        {/* Replay catch-up veil — covers the fast-scroll through a large
            replay parse, reveals the pane already settled at the latest
            content. See CATCHUP_VEIL_MIN_BYTES. */}
        {catchup && (
          <div className={`pane-catchup${catchup === 'fading' ? ' done' : ''}`} aria-hidden />
        )}
        {/* Renderer-switch scrim: masks the fresh xterm's blank/connecting beat
            while the daemon respawns the pane as a terminal (Focus→Terminal
            switch). Mirrors NativePane's scrim in the other direction. */}
        {modeSwitching && (
          <div className="pane-switching-scrim" role="status" aria-live="polite">
            <span className="pane-switching-spin" aria-hidden />
            <span className="pane-switching-label">
              Switching to Terminal — restoring your session…
            </span>
          </div>
        )}
        {canAct() && pane.state === 'choice-prompt' && (
          <ApprovalActions paneId={pane.id} sessionKey={key} actionGuard={actionValid} />
        )}
        {/* Conversation-discontinuity banner — mirrors NativePane's. For an
            interrupted notice, Continue types the resume nudge straight into
            the PTY (submitting it clears the daemon's notice). */}
        {shouldShowSwitchNotice(pane.switchNotice, dismissedNotices) && pane.switchNotice && (
          <div className="pane-switch-notice">
            <SwitchInterruptedBanner
              fromKind={pane.switchNotice.fromKind}
              reason={pane.switchNotice.reason}
              onContinue={() => {
                if(!actionValid())return;
                paneSender?.('Continue where you left off.\r');
                const key = switchNoticeKey(pane.switchNotice);
                if (key != null) setDismissedNotices((s) => new Set(s).add(key));
              }}
              onDismiss={() => {
                if(!actionValid())return;
                const key = switchNoticeKey(pane.switchNotice);
                if (key != null) setDismissedNotices((s) => new Set(s).add(key));
              }}
            />
          </div>
        )}
        {canAct() && paneFind.open && (
          <PaneFindBar
            inputRef={paneFind.inputRef}
            query={paneFind.query}
            setQuery={paneFind.setQuery}
            results={paneFind.results}
            onNext={paneFind.next}
            onPrev={paneFind.prev}
            onClose={paneFind.close}
          />
        )}
        <PaneBodyOverlays
          paneId={pane.id}
          connStatus={connStatus}
          paneStatus={pane.status}
          exitCode={pane.exitCode}
          resumable={pane.resumable}
          onResume={() => {
            // Hand the daemon our live measured viewport so the resumed PTY
            // comes up at the CURRENT window width, not the last-persisted size
            // (post-shutdown / cross-window garble). termRef is still mounted
            // behind the Resume card, refit to the current host by the observer.
            if(!actionValid())return Promise.resolve(null);
            const t = termRef.current;
            return resumePane(pane.id, t?.cols, t?.rows);
          }}
          inputLocked={inputLocked}
          inputLockUnowned={inputLockUnowned}
          dropZone={dropZone}
          beingDragged={beingDragged}
          dictating={dictating}
          dictationPhase={dictationPhase}
          dictationAboutToCancel={dictationAboutToCancel}
          showsReaderChip={showsReaderChip}
          scrolledAway={paneReaderMode.scrolledAway}
          newLinesCount={paneReaderMode.newLinesCount}
          lastOutputMs={paneReaderMode.lastOutputMs}
          isMobileView={isMobileView}
          settling={settling}
          getViewport={getXtermViewport}
          jumpToLive={paneReaderMode.jumpToLive}
        />
        {/* Claim overlay now lives at PaneGrid level — one overlay
            covers the whole terminal area, tap once to claim every
            pane. See PaneGrid.tsx. Per-pane ownership state is kept
            for the xterm input-gate (ownedRef above) and for
            PaneGrid to know when to show the overlay. */}
      </div>
    </div>
  );
}
