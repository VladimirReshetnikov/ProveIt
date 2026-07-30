# Leant (Python) — a GHCi-style interactive REPL for Lean 4

An interactive read-eval-print loop for Lean 4, modeled on Haskell's GHCi.
Type expressions to evaluate them, type declarations to extend the session,
and use `:`-commands for everything else.

## Why this design

There was (as of mid-2026) no interactive human-facing REPL for Lean 4.
The ecosystem provides:

- [leanprover-community/repl](https://github.com/leanprover-community/repl) —
  the machine-oriented backend: JSON over stdin/stdout, environment snapshots.
- [LeanInteract](https://github.com/augustepoiroux/LeanInteract) — a Python
  API that installs/builds the right REPL version automatically (including a
  cross-version fork), works on Windows, and supports running inside a local
  Lake project.
- [lean-repl-py](https://pypi.org/project/lean-repl-py/),
  [Kimina Lean Server](https://arxiv.org/html/2504.21230v1) — programmatic /
  batch-server wrappers, not interactive shells.

`leant.py` is the missing front-end: a single-file GHCi-style shell built
on LeanInteract. Definitions persist between inputs via the backend's
environment threading; the session survives backend crashes (commands are
replayed from a session cache); Ctrl+C restarts the server without losing
your definitions.

## Setup

```
pip install -r requirements.txt
```

Requires Python ≥ 3.10, git, and `lake`/`lean` on PATH (via elan).
The first launch downloads and builds the Lean REPL backend (~5 min);
afterwards startup is instant.

## Usage

```
python leant.py                       # auto-detects the enclosing Lake project
python leant.py --project C:/ProveIt  # explicit Lake project
python leant.py --plain               # bare Lean (no project, stdlib only)
python leant.py -i Mathlib.Tactic.Ring  # start with imports
python leant.py MyFile.lean           # load a file at startup
python leant.py --transcript [FILE]   # record a full session transcript
python leant.py --transcript --timestamps  # ...with per-command timestamps
```

On Windows, `leant.cmd` (in this directory) wraps the above.

This is the Python implementation; the primary implementation is the
Haskell one in [`Tools/Leant`](../Leant/README.md).

When run inside a Lake project (e.g. this repository), all built project
modules and dependencies (Mathlib, ...) are importable. Import narrow
modules (`Mathlib.Tactic.Ring`) rather than all of `Mathlib` when RAM is
tight — a full Mathlib import can take minutes on small machines.

### Example session

```
λ> 2 + 2
4
λ> def fact : Nat → Nat
…>   | 0 => 1
…>   | n + 1 => (n + 1) * fact n
…>
λ> fact 10
3628800
λ> :t fact
fact : Nat → Nat
λ> import Mathlib.Tactic.Ring
λ> example (a b : Nat) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring
λ> example : 1 = 2 := by sorry
sorry (proof state 0)
  ⊢ 1 = 2
```

Bare expressions are evaluated with `#eval`; if that fails (e.g. no `Repr`
instance, or the expression is a proposition or function), the type is shown
via `#check` instead. Declarations (`def`, `theorem`, `open`, `#eval`, ...)
run verbatim and, on success, advance the session environment.

### Prove mode

`:prove PROP` opens an interactive tactic session on `PROP` (and bare
`:prove` resumes the most recent `sorry`):

```
λ> :prove ∀ n : Nat, 0 + n = n
⊢ ∀ (n : Nat), 0 + n = n
⊢> intro n
n : Nat
⊢ 0 + n = n
⊢> induction n
— goal 1 of 2 — ...
⊢2> exact?
recorded as: exact Nat.zero_add 0
⊢> :auto
closed by: simp  (tried rfl, trivial, decide, simp)
All goals accomplished 🎉
⊢> :qed zeroAdd
saved: theorem zeroAdd : ∀ n : Nat, 0 + n = n
```

Goals reprint after every tactic (numbered when there are several; the
prompt shows the count). `:undo [N]` takes back tactics without limit;
`:script` shows the accumulated proof; `:auto` tries common finishers;
`:qed [NAME]` turns the script into a real `theorem` in the session
(auto-named `prove_N`); `:abort` leaves the mode, printing the script.
`?`-tactics (`exact?`, `simp?`, `rw?`) record the tactic they *found*
rather than the question-mark form. If the backend dies or is
interrupted, the script is printed before the mode exits — work is never
lost. When resuming a `sorry`, `:qed` prints a paste-ready `by` block
instead (the original declaration has already elaborated).

The last successfully evaluated expression is available as `it`, GHCi-style
(`2 + 2` then `it * 10` gives `40`). TAB completes `:commands` and dotted
identifiers (via the same cached environment that powers `:browse`, `:doc`,
and `:search` — the first completion builds it).

Multi-line input starts automatically when a line is syntactically
incomplete (unbalanced brackets, trailing `:=`/`by`/`where`/..., or a parse
error at end of input); once started, an empty line submits the block
(Python-REPL style). `:{` ... `:}` delimits an explicit block, as in GHCi.

`:info` renders inductives, structures, and classes as valid Lean
declarations (`inductive Nat : Type where | zero : Nat | succ : Nat → Nat`)
rather than `#print`'s raw "constructors:" listing.

Built-ins and keywords that are not constants in the environment (`imax`,
`Sort`, `fun`, `by`, `→`, `∀`, `:=`, `⟨⟩`, ...) get explanatory help when
used with `:t`/`:info` or evaluated bare, instead of a plain
"Unknown identifier" error.

### Commands

| Command | Meaning |
|---|---|
| `:help`, `:h`, `:?` | show help |
| `:quit`, `:q` | exit |
| `:type EXPR`, `:t` | show the type of an expression (`#check`) |
| `:info NAME`, `:i` | show a definition (`#print`) |
| `:load FILE`, `:l` | reset the session and load a `.lean` file |
| `:reload`, `:r` | reload the last loaded file |
| `:import MOD` | add an import (rebuilds the session, replaying history) |
| `:imports` | list active imports |
| `:browse NS` | list declarations under a namespace (`:browse!` includes generated auxiliaries) |
| `:doc NAME` | show the documentation string of a declaration |
| `:search TEXT` | case-insensitive name search over the environment |
| `:search? TYPE` | proof search: what proves TYPE? (via `exact?`) |
| `:synth TYPE` | term synthesis — Haskell [Tools/Leant](../Leant/README.md) only (in-process Djex engine); here it prints a pointer |
| `:prove [PROP]` | interactive prove mode (see above); bare form resumes the last `sorry` |
| `:set OPT VAL` | `set_option` persisting in the session |
| `:undo` | revert the last state-changing command |
| `:reset` | clear definitions, keep imports |
| `:history` | list state-changing commands |
| `:env` | show the backend environment id |
| `:time` | toggle per-command timing |
| `:transcript [FILE\|on\|off]` | record a full transcript of the session to a file |
| `:timestamps [on\|off]` | timestamp each command in the transcript |
| `:pickle FILE` / `:unpickle FILE` | save/restore the environment as `.olean` |
| `:! CMD` | run a shell command |

### Notes and limitations

- `import` mid-session rebuilds the environment from scratch and replays
  your history (imports cannot be added incrementally to a Lean
  environment). Unavailable modules are detected up front (the backend
  otherwise ignores them silently, yielding an empty environment).
- `sorry` prints its goal and a proof-state id; `:prove` resumes it
  interactively.
- Interrupting evaluation (Ctrl+C) restarts the backend; the session is
  restored automatically from the replay cache on the next command.
- Line history is stored in `~/.leant_history`.
- Transcripts contain the whole session (prompts, inputs, and ANSI-stripped
  output). `--transcript` with no FILE writes `leant-<date>-<time>.log`
  in the current directory. `:transcript` alone shows recording status.
