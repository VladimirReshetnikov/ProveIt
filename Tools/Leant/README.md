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
`→ / × / ∧ / ⊕ / ∨ / ↔ / ¬ / ⊥ / ⊤ / ∀` over opaque variables — plus
inductive datatypes (see below) — using the Djinn LJT engine from the
vendored [Djex](../../lib/Djex) library — linked in-process, no
subprocess. Design and phasing:
[SYNTHESIS_PROPOSAL.md](SYNTHESIS_PROPOSAL.md) (phases 0–2 are
implemented).

```
λ> :synth (A × (B ⊕ C) → (A × B) ⊕ (A × C))
  1  fun ⟨a, b⟩ => match b with | .inl c => .inl ⟨a, c⟩ | .inr d => .inr ⟨a, d⟩
(1 verified candidate)
λ> :synth (∀ p q : Prop, ((p → q) → p) → p)
constructively unprovable — but classically:
  1  fun _ _ f => match Classical.em _ with | .inl x => x | .inr k => f (fun y => absurd y k)
λ> :synth (∀ p : Prop, Decidable p → Decidable (¬ p))
  1  fun _ x => match x with | .isFalse k => .isTrue k | .isTrue y => .isFalse (fun k1 => k1 y)
(1 verified candidate)
```

Binders are named by role — continuations/negations `k`, functions
`f g h`, values `x y z` — and a constructively refuted `Prop` goal gets
a classical attempt: first with an excluded-middle case split per
atomic subformula (shown as `match Classical.em _ with ...`), then via
the Glivenko double-negation translation wrapped in
`Classical.byContradiction`. Both presentations are backend-verified
like every other candidate; single-argument negations render as
`absurd`.

- Every displayed candidate has been **verified by the Lean backend**
  (`example : (T) := term`) — the synthesis engine is never trusted.
  Where a term's shape is ambiguous in Lean (a quantified hypothesis may
  be transported whole or instantiated), the renderer offers the
  alternatives and verification picks the one that elaborates.
- Candidates are ranked smallest-first; `:synth N` binds candidate N as
  `it` (in prove mode it closes the goal with `exact`). Bare `:synth`
  targets the current prove-mode goal or the last `sorry`.
- Negative verdicts are labeled by strength: "provably uninhabited" only
  when the translation was complete and every opaque atom is a genuine
  quantified variable; otherwise "no term found within bounds". In
  `Prop` the verdict notes it is about *constructive* provability.
- Inductive types expand into generalized sums of products (phase 2):
  a non-recursive, non-indexed, non-mutual inductive or structure —
  built-in (`Bool`, `Option`, `Ordering`, `Except`, `Decidable`, ...) or
  session-declared — applied to all of its parameters, whose constructor
  fields are explicit and non-dependent, is declared to the engine as a
  datatype: constructors become introduction rules, case analysis an
  elimination rule. Candidates render with the real constructor names
  (`match a with | Option.none => ... | Option.some b => ...`), and
  refutations over expanded inductives stay sound (the engine saw the
  complete constructor list). Recursive (`Nat`, `List`), indexed (`Eq`),
  and dependent-field (`Exists`, unreduced `Sigma`) types stay atoms.
- Dependent subformulas (`∀ n : Nat, P n`) are carried as opaque atoms:
  transportable, never analyzed. Session declarations are visible to
  goal translation (the session history is replayed into the synthesis
  environment).
- Auto-bound goal variables default to `Sort`; when Type-level `×`/`⊕`
  over arrows leaves Lean's universe unifier stuck, `:synth` retries
  with the unresolved variables bound at `Type` (noted in the output),
  narrowing that set if some variable turns out not to belong at `Type`
  (a `Prop` operand, say). Names that resolve in the session — including
  through an opened namespace — are never shadowed by the retry.
- Explicit `∀` binders — leading, nested, trailing, or interleaved — are
  woven into the candidate's lambda automatically; implicit ones are
  left to the elaborator; and uses of quantified hypotheses get
  placeholder type arguments wherever Lean needs them (`f _ x`,
  `h a _ q`), so bounded rank-N candidates verify.
- A second engine is available: `:set synth-engine exference` switches
  to Djex's ranked heuristic search (explicit budgets, no negative
  verdicts; `:set synth-steps N` bounds it, default 4096), and
  `both` runs the two engines together — Djinn's candidates first,
  Exference's new ones after, refutations only from Djinn. The default
  `djinn` remains the complete, terminating LJT search.
- The engine runs under a wall-clock guard, default 20 s
  (`LEANT_SYNTH_TIMEOUT=N`, `0` waits indefinitely): propositional goals
  answer in microseconds, but bounded hypothesis instantiation can widen
  a quantified goal's space enough to run for minutes. A timeout is
  reported as "no answer", never as a verdict. `LEANT_SYNTH_DEBUG=1`
  prints the translated fragment and the rendered variants, which is the
  fastest way to see why a candidate was dropped.
- The Python implementation deliberately does not grow a synthesis host;
  its `:synth` prints a pointer here.
- Golden transcript tests live in [test/](test/): `bash test/run-tests.sh`
  pipes each `synth-*.txt` through `leant --plain` and diffs the
  filtered output against the checked-in `*.golden`; `-u` regenerates
  the goldens after an intentional behavior change.

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
