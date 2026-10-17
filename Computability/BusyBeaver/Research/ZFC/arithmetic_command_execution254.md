# Command execution: natural comparison and internal composition

The [internal evaluator](arithmetic_command_run254.md) now has an exact
comparison with the existing executor and composition laws that hold in
every IΣ1 model.

[`ArithmeticCommandRunNat254`](../../Lean/BusyBeaver/ZFC/ArithmeticCommandRunNat254.lean)
proves agreement with `Enum254.cexec` for every ordinary command list and
working state. The run at the list's length equals the encoded native
result. List length is at most its shifted word code; absorption preserves
the result up to the evaluator's numerical stopping bound. Total decoding
of both words and working registers then gives agreement for every pair of
natural-number codes, with no validity or fuel assumption. This adapter
does not interpret nonstandard model elements as external finite lists.

[`ArithmeticCommandExecution254`](../../Lean/BusyBeaver/ZFC/ArithmeticCommandExecution254.lean)
proves two laws for arbitrary internal words and working-state codes:

```text
eval(raw+1, state) =
  if step(raw, state) = 0 then 0
  else eval(tail(raw), step(raw, state)-1)

eval(append(left, right), state) =
  if eval(left, state) = 0 then 0
  else eval(right, eval(left, state)-1).
```

Zero denotes halt; successful execution returns its working-state code plus
one. Each subtraction therefore occurs only after a positive successful
result. The empty shifted word remains the identity operation, and shifted
word one executes raw command zero.

To prove append execution, extend a live configuration by appending the fixed
right word. A tick commutes with this operation while the left word remains
active, using the proved rest-pointer invariance. Pointwise Σ1 induction on
time preserves either a synchronized pair of runs or an earlier bounded
witness at which the left run stopped. The drain theorem supplies such a
witness. Absorption and the run semigroup law identify its result with the
chosen numerical terminal time, independently of which time is larger.
No lower bound comparing append's code to the sum of its operands is used,
and the induction fixes the initial registers throughout.

The [natural adapter check](results/arithmetic-command-run-nat254-verification.json)
passes twelve axiom reports and fifteen callers. The
[composition check](results/arithmetic-command-execution254-verification.json)
passes fifteen reports and twenty callers. Both freshly check their new
source and audit, use only standard Lean axioms, and emit no warnings.
Their [independent review](results/arithmetic-command-execution254-review.json)
checks the scopes and exact artifacts. They reuse 22 and 24 matched project
prerequisites respectively. Later portable wrappers pass preparation on the
maintained paths; those preparations invoke no Lean process and are not
claimed as additional proof replays.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_command_run_nat254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --run-evidence /outside/successful-command-run/verification.json \
  --output /outside/new-empty-natural-adapter-check

python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_command_execution254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --run-evidence /outside/successful-command-run/verification.json \
  --word-laws-evidence /outside/successful-word-laws/verification.json \
  --output /outside/new-empty-execution-check
```

These laws now support the checked [fixed compiler-block contracts](arithmetic_command_block_execution254.md)
and [all-internal accepted-proof induction](arithmetic_proof_word_correct254.md).
Scheduler transport, binary traces and the PA consistency equivalence remain
separate obligations; no state count changes here.
