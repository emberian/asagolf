/* tslint:disable */
/* eslint-disable */

/**
 * Version/identity marker so the page can show which kernel it loaded.
 */
export function kernel_id(): string;

/**
 * Look up one label in the parsed DB. Returns
 * `{"ok":true,"label":"..","kind":"$p","statement":"|- ..",
 *   "hyps":[..],"proof":[..],"proof_len":K}` or `{"ok":false,...}`.
 *
 * `proof` (the stored RPN label list) is returned in full; the page lazily
 * renders it. For non-`$p` statements `proof` is `[]`.
 */
export function lookup(src: string, label: string): string;

/**
 * Parse once and return a JSON object of useful summary data plus a label
 * index, so the page can do parse+verify+browse with a single WASM call.
 *
 * `{"ok":true,"statements":N,"provable":M,"verified":bool,
 *   "error":<null|str>,"labels":["id","syl",...]}`
 */
export function parse_summary(src: string): string;

/**
 * Parse a `.mm` source string and run the kernel's `verify()` over every
 * `$p`. Returns a JSON object:
 *
 * `{"ok":true,"statements":N,"provable":M}` on success, or
 * `{"ok":false,"error":"...","stage":"parse"|"verify"}` on rejection.
 *
 * This is the genuine trust boundary made interactive: the verdict is
 * exactly what the native kernel would return for the same bytes.
 */
export function verify(src: string): string;

export type InitInput = RequestInfo | URL | Response | BufferSource | WebAssembly.Module;

export interface InitOutput {
    readonly memory: WebAssembly.Memory;
    readonly kernel_id: () => [number, number];
    readonly lookup: (a: number, b: number, c: number, d: number) => [number, number];
    readonly parse_summary: (a: number, b: number) => [number, number];
    readonly verify: (a: number, b: number) => [number, number];
    readonly __wbindgen_externrefs: WebAssembly.Table;
    readonly __wbindgen_free: (a: number, b: number, c: number) => void;
    readonly __wbindgen_malloc: (a: number, b: number) => number;
    readonly __wbindgen_realloc: (a: number, b: number, c: number, d: number) => number;
    readonly __wbindgen_start: () => void;
}

export type SyncInitInput = BufferSource | WebAssembly.Module;

/**
 * Instantiates the given `module`, which can either be bytes or
 * a precompiled `WebAssembly.Module`.
 *
 * @param {{ module: SyncInitInput }} module - Passing `SyncInitInput` directly is deprecated.
 *
 * @returns {InitOutput}
 */
export function initSync(module: { module: SyncInitInput } | SyncInitInput): InitOutput;

/**
 * If `module_or_path` is {RequestInfo} or {URL}, makes a request and
 * for everything else, calls `WebAssembly.instantiate` directly.
 *
 * @param {{ module_or_path: InitInput | Promise<InitInput> }} module_or_path - Passing `InitInput` directly is deprecated.
 *
 * @returns {Promise<InitOutput>}
 */
export default function __wbg_init (module_or_path?: { module_or_path: InitInput | Promise<InitInput> } | InitInput | Promise<InitInput>): Promise<InitOutput>;
