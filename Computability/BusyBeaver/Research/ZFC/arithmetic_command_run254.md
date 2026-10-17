# Internal execution of coded command words

[`ArithmeticCommandTick254`](../../Lean/BusyBeaver/ZFC/ArithmeticCommandTick254.lean)
and [`ArithmeticCommandRun254`](../../Lean/BusyBeaver/ZFC/ArithmeticCommandRun254.lean)
give fixed arithmetic graphs for execution of a shifted command word.
Every internal word terminates in every IΣ1 model: it either encounters a
halting NIP or completes successfully. These are distinct outcomes. PA
proves a closed arithmetic sentence asserting unique totality of the evaluator.

A live configuration is `P(remainingWord, workingState) + 1`; zero denotes
halt. A positive configuration with remaining word zero denotes completion.
Both stopped configurations are absorbing. An active tick removes the
word's positive marker once, executes its actual raw head through the
[command-step graph](arithmetic_command_step254.md), and takes its represented
tail. Thus shifted word one executes raw command zero (`MP 0`), whereas
shifted word zero successfully returns the input state.

An active tick either halts or strictly decreases the remaining word code,
independently of growth in the working registers. For fixed initial word and
state, Σ1 induction on internal time proves

```text
Stopped(run(time, live(word, state)))
  or remaining(run(time, live(word, state))) + time <= word.
```

At time `word`, the remaining code must be zero unless the run has already
halted. The induction predicate contains a single changing evaluator with
fixed parameters; it does not assume a universally quantified induction
hypothesis over arbitrary changing working states. The proof covers internal
model elements without interpreting them as ordinary finite lists.

The run graph satisfies its exact zero/successor recurrence, absorption at
all internal times, and the semigroup identity
`run(a+b,c) = run(b,run(a,c))`. The evaluator examines the stopped configuration
at time `word` and returns zero for halt or final working-state code plus one
for completion. In particular, evaluation of the empty word returns `state+1`.
The fixed run and evaluation graphs have Σ1 and Δ1 definitions. Arithmetic
completeness converts their all-model unique-totality result into actual
IΣ1 and PA derivability of the stated totality sentence.

The [verification](results/arithmetic-command-run254-verification.json)
freshly checks both modules and an audit with twenty-five axiom reports and
thirty callers, using only standard Lean axioms and no warnings. It reuses
twenty source/object-matched project prerequisites and identifies the actual
external providers; no dependency rebuild is claimed. The
[independent review](results/arithmetic-command-run254-review.json) checks
the model scope, zero conventions, induction predicate and exact artifacts.
The final portable wrapper has also passed preparation on the maintained
paths. That preparation invokes no Lean process and is recorded separately
from the successful kernel run of the unchanged sources and audit.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_command_run254.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/dependency-checkout \
  --step-word-evidence /outside/successful-command-step-word-check/verification.json \
  --append-evidence /outside/successful-command-append-check/verification.json \
  --output /outside/new-empty-command-run-check
```

The append record supplies the checked PRF/Seq providers; this check does not
import the append module's object. The next obligations are agreement with
the existing natural-number `cexec`, execution of appended words, and the
accepted-proof compiler contract. Scheduler and binary-trace transport and
the PA consistency equivalence remain open. No machine transition or state
count changes here.
