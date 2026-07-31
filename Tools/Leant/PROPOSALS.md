# Leant — proposed improvements and new features

Applies to both implementations (Python `Tools/LeantPy`, Haskell
`Tools/Leant`) unless marked otherwise. Ordered by expected
value-for-effort within each tier. Effort: S (< half a day), M (a day or
two), L (several days).

Term-synthesis (`:synth`) proposals live in
[SYNTHESIS_PROPOSAL.md §7](SYNTHESIS_PROPOSAL.md#7-post-phase-2-proposals):
prove-mode hypotheses as premises, a Glivenko classical fallback,
golden transcript tests, recursive-inductive constructors as premises,
rendering polish, and the Exference engine on-ramp.

## Tier 1 — high value, backend already supports it

### 1. Interactive proof mode (`:prove`) — L, flagship
The backend's tactic mode is completely unused. `sorry` responses already
carry `proof_state` ids, and a `{"tactic": ..., "proofState": N}` request
applies one tactic and returns the new goals and a `proof_status`
(`Completed` / `Incomplete` / errors).

Proposed UX, GHCi-meets-`gdb` style:

```
λ> :prove ∀ n : Nat, 0 + n = n
⊢ ∀ (n : Nat), 0 + n = n
⊢> intro n
n : Nat ⊢ 0 + n = n
⊢> induction n
2 goals ...
⊢> :undo            -- pop one tactic
⊢> simp
Goals accomplished 🎉
theorem recorded as `prove_1` (:name to rename); :qed to return
```

- `:prove EXPR` elaborates `example : EXPR := by sorry`, captures the
  proof state, switches the prompt to `⊢>`.
- Every input line is a tactic; `:undo` pops the proof-state stack;
  `:goals` reprints; `:qed`/`:abort` exit the mode. On completion, the
  accumulated tactic script is assembled into a `theorem` and replayed
  into the session env, so the result is *usable* afterwards.
- Also entered via `:prove NAME` on an existing `sorry` in the session.

### 2. Identifier tab-completion — M
We already build a cached "browse environment". Reuse it for completion:
on TAB over a partial dotted name, run a (cached, prefix-filtered) variant
of the `:browse` metaprogram and feed the candidates to Haskeline /
prompt_toolkit. Session-declared names come from history parsing (already
implemented for `:browse`). Cache per (browse-env, first-component) to
keep it snappy. This is the single biggest day-to-day ergonomics win.

### 3. `:doc NAME` — S
Print a declaration's docstring: metaprogram in the browse env,
`findDocString? env name`, falling back to signature via `#check @NAME`.
Pairs naturally with `:info`.

### 4. `:search` (name and type search) — M
- `:search foo` — substring/fuzzy match over constant names (same
  fold over `env.constants` as `:browse`).
- `:search? TYPE` — proof search for a goal: elaborate
  `example : TYPE := by exact?` and show what `exact?` finds (works
  whenever Mathlib's `exact?` is importable). This turns the REPL into a
  practical "is this already proven?" tool.

### 5. One-shot / scripting mode (`-e`, `--script`) — S
`leant -e "2 + 2"` evaluates and exits with the result on stdout
(exit code reflects errors); `leant --script file.repl` runs a
transcript of REPL inputs. Makes the REPL usable from Makefiles, CI
checks, and editor keybindings. The non-tty path already does 90% of
this — it needs only flag plumbing and quieter output.

### 6. `it` binding — S
GHCi-style: after a successful expression evaluation, bind the value as
`it` (`def it := (<expr>)` threaded into the env, replacing prior `it`).
Enables `double 21` … `it + 1`. Cheap because env threading is already
the core mechanism; skip binding when elaboration of the `def` fails
(e.g. universe-polymorphic or noncomputable values).

## Tier 2 — quality of life

### 7. `:save FILE` (session → .lean file) — S
Write imports + history as a well-formed `.lean` file (the inverse of
`:load`). The transcript records everything including errors; `:save`
records only the *surviving* declarations — the thing you actually want
to keep after an exploratory session. `:pickle` complements but is
binary and toolchain-bound.

### 8. Config file (`~/.leantrc` / project `.leantrc`) — S
Default imports, default `set_option`s, timeout, color and timestamp
preferences, default transcript directory. Project-level file overrides
user-level. Removes per-invocation flag noise for the ProveIt workflow
(e.g. always `-i Mathlib.Tactic.Ring` in this repo).

### 9. `:undo N` and `:redo` — S
`:undo 3` pops three states; `:redo` restores the last undone entry
(keep a redo stack cleared on new input). The env-stack machinery
already exists; this is bookkeeping.

### 10. Richer `:set`/`:show` — S
`:show options` (run `#print options`... actually: track the session's
`set_option` history and display it), `:show imports`, `:show env`,
`:show paths` (project, backend, toolchain). GHCi users expect `:show`.

### 11. Background Mathlib warm-up — M (Python), M/L (Haskell)
`--warm Mathlib` (or config default): start importing in a second
backend process at launch; swap it in when ready. Hides the ~1-3 min
Mathlib import behind the user's first few plain-stdlib interactions.
On this machine (13 GB RAM) it must be opt-in.

### 12. Goal pretty-printing — S
Colorize goal displays: hypothesis names dim, `⊢` bold, error underlines
under the caret span (positions are already in every message). Applies
to `sorry` output today and `:prove` tomorrow.

## Tier 3 — architectural / parity

### 13. Backport Haskell's `:browse` to Python — S
The Python `:browse` still requires `:import Lean` and lists unfiltered
constants. Port back the side-environment cache, `isInternalDetail`
filtering, `:browse!`, `@`-stripping, and session-declaration section.

### 14. Self-managing backend in Haskell — M
`leant` (the Haskell implementation) currently reuses the binary LeanInteract built. Teach it to
clone and `lake build` the matching REPL revision itself (toolchain read
from `lean-toolchain`), making the Haskell port fully standalone.

### 15. `:load` incremental reload — L
`:reload` currently re-elaborates the whole file. The backend supports
incremental elaboration (`incrementality` flag in the fork); wiring it in
would make the edit-reload loop close to instant for small changes.

### 16. Structured JSON output mode (`--json`) — M
Mirror every response (messages, sorries, env ids, timing) as JSON lines
on stdout. Turns the REPL into a backend for editor plugins and agents
while keeping the human UI as-is. (The Python version could expose the
LeanInteract objects almost directly.)

## Explicitly not proposed

- A GUI / web front-end: `lean4_jupyter` already covers notebook use.
- Replacing the backend protocol: the blank-line JSON framing is crude
  but works on all platforms; changing it buys nothing user-visible.
- Windows-specific installers: `leant.cmd` + PATH is adequate.
