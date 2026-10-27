import { beforeEach, describe, expect, it, vi } from 'vitest';
import { attachPaneMousePasteHandlers } from './paneMousePaste';

const { state } = vi.hoisted(() => ({ state: { copyOnSelect: true, middleClickPaste: true } }));
vi.mock('../store', () => ({ useStore: { getState: () => state } }));

function setup(overrides: Partial<Parameters<typeof attachPaneMousePasteHandlers>[0]> = {}) {
  const host = document.createElement('div');
  const term = { paste: vi.fn(), getSelection: vi.fn(() => '') };
  const copy = vi.fn();
  const release = vi.fn();
  const cleanup = attachPaneMousePasteHandlers({
    hostEl: host, term, ownedRef: { current: true }, canAct: () => true,
    beginInteraction: () => release, captureGuard: () => () => true,
    copy, readClipboard: async () => 'one\r\ntwo\r\n', ...overrides,
  });
  return { host, term, copy, release, cleanup };
}

function mouse(host: HTMLElement, type: string, button: number): MouseEvent {
  const e = new MouseEvent(type, { button, bubbles: true, cancelable: true });
  host.dispatchEvent(e);
  return e;
}

beforeEach(() => {
  state.copyOnSelect = true;
  state.middleClickPaste = true;
});

describe('attachPaneMousePasteHandlers', () => {
  it('routes multi-line clipboard text through term.paste', async () => {
    const { host, term, release } = setup();
    const e = mouse(host, 'mousedown', 1);

    await vi.waitFor(() => expect(term.paste).toHaveBeenCalledTimes(1));
    expect(term.paste).toHaveBeenCalledWith('one\r\ntwo\r\n');
    expect(e.defaultPrevented).toBe(true);
    expect(release).toHaveBeenCalledTimes(1);
  });

  it('does nothing when middle-click paste is disabled or the pane is not owned', async () => {
    state.middleClickPaste = false;
    let { host, term } = setup();
    mouse(host, 'mousedown', 1);
    await Promise.resolve();
    expect(term.paste).not.toHaveBeenCalled();

    state.middleClickPaste = true;
    ({ host, term } = setup({ ownedRef: { current: false } }));
    mouse(host, 'mousedown', 1);
    await Promise.resolve();
    expect(term.paste).not.toHaveBeenCalled();
  });

  it('copies the selection on left-button mouseup', () => {
    const { host, copy } = setup({ term: { paste: vi.fn(), getSelection: () => 'selected text' } });
    mouse(host, 'mouseup', 0);
    expect(copy).toHaveBeenCalledWith('selected text');
  });
});
