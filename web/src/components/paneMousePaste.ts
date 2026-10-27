import type { MutableRefObject } from 'react';
import { useStore } from '../store';

export interface MousePasteTerminal {
  paste(text: string): void;
  getSelection(): string;
}

interface AttachPaneMousePasteHandlersOpts {
  hostEl: HTMLElement | null;
  term: MousePasteTerminal;
  ownedRef: MutableRefObject<boolean | null>;
  canAct: () => boolean;
  beginInteraction: () => (() => void) | null;
  captureGuard: () => () => boolean;
  copy?: (text: string) => void | Promise<unknown>;
  readClipboard?: () => Promise<string | undefined>;
}

// X11 primary-selection convention: copy-on-select + middle-click paste.
export function attachPaneMousePasteHandlers({
  hostEl, term, ownedRef, canAct, beginInteraction, captureGuard, copy, readClipboard,
}: AttachPaneMousePasteHandlersOpts): () => void {
  const copyText = copy ?? ((text: string) => navigator.clipboard.writeText(text));
  const readText = readClipboard ?? (() => Promise.resolve(navigator.clipboard?.readText?.()));

  const onMouseUp = (e: MouseEvent) => {
    if (!canAct() || e.button !== 0) return;
    if (!useStore.getState().copyOnSelect) return;
    const sel = term.getSelection();
    if (sel) void copyText(sel);
  };

  // Middle-click paste fires on press, so handle mousedown and prevent the
  // browser's autoscroll. Ride xterm's paste path so CRLF and bracketed
  // paste behave like a normal paste instead of one Enter per line.
  const onMouseDown = (e: MouseEvent) => {
    if (e.button !== 1) return;
    if (!useStore.getState().middleClickPaste) return;
    e.preventDefault();
    if (ownedRef.current !== true || !canAct()) return;
    const releaseInteraction = beginInteraction();
    if (!releaseInteraction) return;
    const gesture = captureGuard();
    void Promise.resolve(readText()).then((text) => {
      if (!gesture() || ownedRef.current !== true || !text) return;
      term.paste(text);
    }).catch(() => {}).finally(releaseInteraction);
  };

  hostEl?.addEventListener('mouseup', onMouseUp);
  hostEl?.addEventListener('mousedown', onMouseDown);
  return () => {
    hostEl?.removeEventListener('mouseup', onMouseUp);
    hostEl?.removeEventListener('mousedown', onMouseDown);
  };
}
