package main

import (
	"errors"
	"os"
	"os/exec"
	"testing"
)

// The two shapes Wait can leave behind: an *exec.ExitError (Unix, and pipe
// mode on Windows), and — with go-pty's ConPTY command on Windows — a nil
// error whose status is only in the command's ProcessState.
func TestExitCodeFromWait(t *testing.T) {
	if os.Getenv("SOLUTERMINAL_EXIT_CODE_HELPER") == "1" {
		os.Exit(7)
	}
	cmd := exec.Command(os.Args[0], "-test.run=^TestExitCodeFromWait$")
	cmd.Env = append(os.Environ(), "SOLUTERMINAL_EXIT_CODE_HELPER=1")
	err := cmd.Run()
	var ee *exec.ExitError
	if !errors.As(err, &ee) {
		t.Fatalf("helper process: err = %v, want *exec.ExitError", err)
	}
	if got := exitCodeFromWait(err, nil); got != 7 {
		t.Errorf("from the ExitError = %d, want 7", got)
	}
	if got := exitCodeFromWait(nil, cmd.ProcessState); got != 7 {
		t.Errorf("from the ProcessState = %d, want 7", got)
	}
	if got := exitCodeFromWait(nil, nil); got != 0 {
		t.Errorf("no error, no state = %d, want 0", got)
	}
	if got := exitCodeFromWait(errors.New("wait failed"), nil); got != -1 {
		t.Errorf("other error = %d, want -1", got)
	}
}
