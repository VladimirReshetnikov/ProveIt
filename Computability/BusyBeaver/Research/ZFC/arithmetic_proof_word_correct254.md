# Compiler correctness for every internal proof code

[`ArithmeticProofWordCorrect254`](../../Lean/BusyBeaver/ZFC/ArithmeticProofWordCorrect254.lean)
closes the accepted-proof execution contract in every IΣ1 model, including
at nonstandard proof codes. For any code accepted by the unchanged validator,
its raw compiled word either halts or returns the validated conclusion from
every initial top and saved stack:

```text
value(code) ≠ 0  implies, for every top and stack,
  eval(rawWord(code), state(top, stack, 0, 0)) = 0
  or
  eval(rawWord(code), state(top, stack, 0, 0))
    = state(value(code)-1, stack, 0, 0)+1.
```

The same contract holds for the public gated `compiledWord`. Zero denotes
halt; a positive result is the successful working-state code plus one.

The proof uses the [Π1 contract interface](arithmetic_proof_word_contract254.md).
`row_contract` checks all twelve cases of the actual validator and compiler
row. It retains both MP acceptance markers, the whole-tail GEN child, all
original axiom argument projections and both bundle freshness gates. A
nonzero row result excludes malformed truth payloads and out-of-range tags.
The [fixed block contracts](arithmetic_command_block_execution254.md) then
supply the execution result in each accepted case.

`good_succ` combines that row theorem with the exact internal histories and
their child bounds. All child contracts therefore belong to the preceding
bounded prefix. `good_all` applies Π1 induction to discharge the previously
explicit successor premise. Universal top/stack quantifiers stay inside the
contract, so the MP major can use its changed stack without a register-growth
bound. No external finite-tree interpretation of internal codes is assumed.

The [fresh check](results/arithmetic-proof-word-correct254-verification.json)
passes five axiom reports and thirteen callers, including MP, GEN, bundle,
invalid-zero and falsity-target instances. It reuses 37 source/object-matched
project modules, uses only standard Lean axioms and emits no warnings.
The [independent review](results/arithmetic-proof-word-correct254-review.json)
checks the full source, audit, arithmetic scope and exact dependencies.
The maintained portable wrapper passes preparation; that later preparation
does not repeat the Lean proof check.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_proof_word_correct254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --rule-evidence /outside/successful-rule/verification.json \
  --output /outside/new-empty-correctness-check
```

The next [refutation-word theorem](arithmetic_refutation_word254.md) uses
this contract to construct a word halting from every working state. Scheduler
transport, command-halting soundness, binary traces and internal C254/ZFC
proof transformations remain separate obligations for the requested PA
consistency equivalence. The machine remains at 252 states.
