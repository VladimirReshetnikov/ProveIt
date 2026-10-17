# Internal execution of the actual compiler blocks

The fixed compiler blocks now satisfy their execution contracts in every
IΣ1 model. All operands and working registers may be internal model elements.
The blocks are the existing compiler circuits, with their original AX gates,
stack pushes and cleanup counts.

[`ArithmeticCommandBlockExecution254`](../../Lean/BusyBeaver/ZFC/ArithmeticCommandBlockExecution254.lean)
derives command-cons equations from the represented evaluator and proves
the discard block's contract. A finite-list lemma describes consecutive NIPs:
the incoming cache and skipped entries must differ from falsity, but the
last loaded entry may be falsity because no further NIP follows it. These
external finite lists describe fixed block layouts; their entries are
arbitrary internal values.

[`ArithmeticCommandLeafExecution254`](../../Lean/BusyBeaver/ZFC/ArithmeticCommandLeafExecution254.lean)
uses that lemma to select each of the eight original logical axiom rows and
restore the saved stack. The bundle contract retains both original freshness
conditions, `c ≠ a` and `c ≠ b`, and permits `a = b`.

[`ArithmeticCommandRuleExecution254`](../../Lean/BusyBeaver/ZFC/ArithmeticCommandRuleExecution254.lean)
proves the GEN and MP contracts. The MP major runs with top zero and the
minor's conclusion pushed onto the original saved stack. The cleanup halts
when it encounters falsity; otherwise it returns the specified conclusion
with accumulator/cache zero and the saved stack restored. Thus each contract
allows either a halt or the exact successful result. The actual circuit
binding lemmas connect these equations to the word-history row.

| Fresh source and audit | Axiom reports | Callers | Reused project modules | Warnings |
| --- | ---: | ---: | ---: | ---: |
| [Block](results/arithmetic-command-block-execution254-verification.json) | 19 | 20 | 34 | 0 |
| [Leaf](results/arithmetic-command-leaf-execution254-verification.json) | 12 | 12 | 35 | 0 |
| [Rule](results/arithmetic-command-rule-execution254-verification.json) | 11 | 8 | 36 | 6 |

All probes use only standard Lean axioms. The Rule warnings identify unused
`simp` arguments; the checked source and its logs are preserved unchanged.
Independent reviews cover the [Block and Leaf](results/arithmetic-command-block-execution254-review.json)
proofs and [Rule](results/arithmetic-command-rule-execution254-review.json)
proofs. Maintained portable wrappers pass preparation with the same checked
sources; preparation invokes no Lean process and is separate from the
successful proof checks above.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_command_block_execution254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --framework-evidence /outside/successful-contract/verification.json \
  --execution-evidence /outside/successful-execution/verification.json \
  --output /outside/new-empty-block-check

python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_command_leaf_execution254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --block-evidence /outside/successful-block/verification.json \
  --output /outside/new-empty-leaf-check

python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_command_rule_execution254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --leaf-evidence /outside/successful-leaf/verification.json \
  --output /outside/new-empty-rule-check
```

These contracts discharge the row cases in the subsequent
[all-internal compiler correctness theorem](arithmetic_proof_word_correct254.md).
They introduce no new calculus or smaller machine table.
