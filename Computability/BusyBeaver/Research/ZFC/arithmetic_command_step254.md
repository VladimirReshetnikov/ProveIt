# Arithmetic execution of one actual command

[`ArithmeticCommandStep254`](../../Lean/BusyBeaver/ZFC/ArithmeticCommandStep254.lean)
represents the working-register effect of the actual `Enum254` commands in
every IOpen model. Its fixed arithmetic graph is total on every raw command
and working-state code. On ordinary natural inputs it agrees with the existing
`Enum254.cstep` for every command, rest pointer and working state.

The working registers are `(t, s, d, h)`: current formula, theorem stack,
additive parameter and cached formula. The unshifted state code is
`P(t, P(s, P(d, h)))`. An output of zero means a halting NIP; a successful
command returns its new state code plus one. Thus a successful all-zero state
has output one and is distinct from halting.

| Command | Exact effect |
| --- | --- |
| MP x | Set `d' = d+x`. If `Imp(t,d') = h`, return `(d', P(0,s), d', 0)`; otherwise return `(0,s,d',0)`. |
| DROP x | Return `(h, P(t,s), d+x, h)`. |
| NIP x | Halt if `h = 1`; otherwise return `(t, second(s), d+x, first(s))`. |
| AX c x y u | Let `a=d+x`, `b=h+y`. Push the eight axiom instances, `All(a,h)`, and the old top in the original order; set `d=h=0` and return the freshness-gated bundle as top. |

The MP test is literal formula-code equality. It has no proof-checker
predecessor or positivity gate. A failed MP continues with truth code zero.
An AX freshness collision also returns top zero while still pushing all ten
entries. Both freshness exclusions remain; equality of `a` and `b` is allowed.
The theorem `stepValue_eq_zero_iff` proves that the sole halting case is the
NIP tag with cache one, at every internal input.

The formula uses unbounded Σ1 witnesses for intermediate values. It does not
bound an intermediate stack or formula by a possibly zero final result.
Raw command zero is the real command `MP 0`; this interface does not consume
an empty shifted word.

The small
[`ArithmeticCommandStepWord254`](../../Lean/BusyBeaver/ZFC/ArithmeticCommandStepWord254.lean)
bridge proves that replacing a raw command's rest pointer preserves its
working-register effect. For AX it preserves every command argument. For
MP, DROP and NIP, extra projections of the new rest may differ, but those
arguments are unused. The short-tag split covers every internal value below
three. This identity is needed for later composition of word executions.

The [command verification](results/arithmetic-command-step254-verification.json)
checks seventeen axiom reports and nineteen callers. The
[rest-pointer verification](results/arithmetic-command-step-word254-verification.json)
checks three reports and four callers. Both have only standard Lean axioms
and no warnings. The [independent review](results/arithmetic-command-step254-review.json)
checks the actual command semantics, all-input graphs, natural-number
adapters and rest-pointer invariance. Existing matched project and dependency
objects are reused; no whole dependency rebuild is claimed. The checked
source/audit pairs are unchanged from the successful kernel runs. The later
portable wrappers pass separate preparation checks on the maintained paths;
those preparation checks do not invoke Lean or constitute another replay.

The portable checkers accept explicit successful prerequisite records,
optional relocated caches and a fresh external scratch directory:

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_command_step254.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/dependency-checkout \
  --core-evidence /outside/successful-native-command-check/verification.json \
  --history-evidence /outside/successful-arithmetic-history-check/verification.json \
  --output /outside/new-empty-command-step-check

python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_command_step_word254.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/dependency-checkout \
  --step-evidence /outside/successful-command-step-check/verification.json \
  --word-evidence /outside/successful-word-laws-check/verification.json \
  --output /outside/new-empty-command-step-word-check
```

The subsequent [internal iterator](arithmetic_command_run254.md) distinguishes
halt from completion, makes both absorbing, and proves that every active
tick decreases the remaining shifted word. Agreement with natural command
execution, append execution, compiled-proof contracts, scheduler transport
and the PA consistency equivalence remain open. These modules change no
machine transition or state count.
