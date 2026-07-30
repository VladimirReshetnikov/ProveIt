# Leant (Haskell) — a GHCi-style interactive REPL for Lean 4

Haskell port of [Tools/LeantPy](../LeantPy/README.md) (the Python
original). Same features, same commands, same heuristics — but a native
binary with no Python dependency at runtime.

## How the port replaces its dependencies

The Python version delegates backend management to
[LeanInteract](https://github.com/augustepoiroux/LeanInteract). This port
implements that layer directly (`src/Leant/Backend.hs`):

- **Backend discovery** — finds the `repl.exe` that LeanInteract built
  (searching its cache under `%LOCALAPPDATA%\Python\...\lean_interact\cache`),
  or uses `--repl-exe` / the `LEANT_BACKEND` environment variable. Any
  build of [leanprover-community/repl](https://github.com/leanprover-community/repl)
  matching the project toolchain works.
- **Protocol** — JSON over stdin/stdout with blank-line framing, spawned as
  `lake env repl.exe` inside the Lake project. The JSON codec is hand-rolled
  (`src/Leant/Json.hs`), so the whole port builds with GHC boot libraries
  only — no Hackage downloads.
- **Crash recovery** — replaces LeanInteract's `AutoLeanServer`: on backend
  death, timeout, or Ctrl+C, the process is killed and the session (imports +
  history) replays automatically on the next command.

The Haskeline front-end (interrupt-safe step loop, logical multi-line input,
`:command` completion) follows the structure of the Djex REPL driver.

## Building

Requires GHC 9.12.4 and cabal. The REPL core uses GHC boot libraries
only, but `:synth` links the vendored [Djex](../../lib/Djex) synthesis
library (a read-only git submodule — run
`git submodule update --init lib/Djex` once), which pulls
`haskell-src-exts` and a few other packages from Hackage. The bundled
`cabal.project` builds both packages together:

```
cabal build exe:leant
```

`leant.cmd` builds on first use and runs the binary (pausing on error
exit, like the Python launcher).

## Usage

Identical to the Python version — see its [README](../LeantPy/README.md)
for the full command table and semantics. Summary:

```
leant [FILE] [--project DIR] [--plain] [-i MOD]
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
- `:doc NAME` shows docstrings; `:search TEXT` searches declaration names
  case-insensitively; `:search? TYPE` runs `exact?` proof search; the last
  evaluated expression is available as `it`; TAB completes `:commands`
  and dotted identifiers.
- `:prove [PROP]` enters interactive prove mode (see the Python README for
  a walkthrough): tactic-by-tactic goals, unlimited `:undo`, `:script`,
  `:auto`, `:qed [NAME]` saving a real theorem, resumption of the last
  `sorry`, and crash-safe script dumps.

## `:synth` — automatic term synthesis (Haskell-only)

`:synth TYPE` constructs programs and proofs in the structural fragment
`→ / × / ∧ / ⊕ / ∨ / ↔ / ¬ / ⊥ / ⊤ / ∀` over opaque variables, using the
Djinn LJT engine from the vendored [Djex](../../lib/Djex) library —
linked in-process, no subprocess. Design and phasing:
[SYNTHESIS_PROPOSAL.md](SYNTHESIS_PROPOSAL.md) (phases 0–1 are
implemented).

```
λ> :synth (A × (B ⊕ C) → (A × B) ⊕ (A × C))
  1  fun ⟨a, b⟩ => match b with | .inl c => .inl ⟨a, c⟩ | .inr d => .inr ⟨a, d⟩
(1 verified candidate)
λ> :synth (((a → b) → a) → a)
provably uninhabited — no closed term of this polymorphic type exists
```

- Every displayed candidate has been **verified by the Lean backend**
  (`example : (T) := term`) — the synthesis engine is never trusted.
- Candidates are ranked; `:synth N` binds candidate N as `it` (in prove
  mode it closes the goal with `exact`). Bare `:synth` targets the
  current prove-mode goal or the last `sorry`.
- Negative verdicts are labeled by strength: "provably uninhabited" only
  when the translation was complete and every opaque atom is a genuine
  quantified variable; otherwise "no term found within bounds". In
  `Prop` the verdict notes it is about *constructive* provability.
- Dependent subformulas (`∀ n : Nat, P n`) are carried as opaque atoms:
  transportable, never analyzed. Session declarations are visible to
  goal translation (the session history is replayed into the synthesis
  environment).
- The Python implementation deliberately does not grow a synthesis host;
  its `:synth` prints a pointer here.

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
  lake build`, then point `LEANT_BACKEND` at
  `.lake/build/bin/repl.exe`.
