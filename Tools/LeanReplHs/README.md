# LeanRepl (Haskell) — a GHCi-style interactive REPL for Lean 4

Haskell port of [Tools/LeanRepl](../LeanRepl/README.md) (the Python
original). Same features, same commands, same heuristics — but a native
binary with no Python dependency at runtime.

## How the port replaces its dependencies

The Python version delegates backend management to
[LeanInteract](https://github.com/augustepoiroux/LeanInteract). This port
implements that layer directly (`src/LeanRepl/Backend.hs`):

- **Backend discovery** — finds the `repl.exe` that LeanInteract built
  (searching its cache under `%LOCALAPPDATA%\Python\...\lean_interact\cache`),
  or uses `--repl-exe` / the `LEANREPL_BACKEND` environment variable. Any
  build of [leanprover-community/repl](https://github.com/leanprover-community/repl)
  matching the project toolchain works.
- **Protocol** — JSON over stdin/stdout with blank-line framing, spawned as
  `lake env repl.exe` inside the Lake project. The JSON codec is hand-rolled
  (`src/LeanRepl/Json.hs`), so the whole port builds with GHC boot libraries
  only — no Hackage downloads.
- **Crash recovery** — replaces LeanInteract's `AutoLeanServer`: on backend
  death, timeout, or Ctrl+C, the process is killed and the session (imports +
  history) replays automatically on the next command.

The Haskeline front-end (interrupt-safe step loop, logical multi-line input,
`:command` completion) follows the structure of the Djex REPL driver.

## Building

Requires GHC ≥ 9.4 and cabal (tested with GHC 9.12.4). All dependencies are
GHC boot libraries:

```
cabal build
```

`leanrepl-hs.cmd` builds on first use and runs the binary (pausing on error
exit, like the Python launcher).

## Usage

Identical to the Python version — see its [README](../LeanRepl/README.md)
for the full command table and semantics. Summary:

```
leanrepl-hs [FILE] [--project DIR] [--plain] [-i MOD]
            [--timeout N] [--time] [--transcript [FILE]] [--timestamps]
            [--repl-exe PATH] [--lake PATH]
```

- Expressions evaluate via `#eval` with `#check` fallback; declarations
  persist via environment threading.
- Multi-line input starts on incomplete lines (or `:{ :}`); a blank line
  submits.
- `:info` renders inductives/structures/classes as valid Lean declarations
  and indents definition bodies; built-ins and keywords (`imax`, `fun`,
  `→`, ...) get explanatory help instead of "Unknown identifier".
- `:transcript` / `:timestamps` record the full session; `:pickle` /
  `:unpickle` save and restore environments; `:undo`, `:reset`,
  `:history`, `:import`, `:load`/`:reload`, `:set`, `:time`, `:!` as in
  the Python version.

## Differences from the Python version

- No `AutoLeanServer` memory guard (the Python version needs one because
  LeanInteract refuses to start above a RAM threshold); the backend is only
  restarted on actual failure.
- `:browse` is *improved* rather than merely ported. The Python version
  required `:import Lean` in the user's session first; here `:browse NS`
  builds (and caches) a separate environment - session imports plus
  `Lean.Elab.Command` - runs the introspection metaprogram there, and
  appends declarations made in the session itself. Compiler-generated
  auxiliaries (`.rec`, `.noConfusion`, `.eq_1`, ...) are filtered out;
  `:browse! NS` shows everything.
- Backend discovery reuses the binary LeanInteract built rather than
  building its own. To set one up from scratch:
  `git clone https://github.com/leanprover-community/repl && cd repl &&
  lake build`, then point `LEANREPL_BACKEND` at
  `.lake/build/bin/repl.exe`.
