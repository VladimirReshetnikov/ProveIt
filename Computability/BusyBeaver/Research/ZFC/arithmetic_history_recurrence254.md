# Internal recurrence and premise validity

[`ArithmeticHistoryRecurrence254`](../../Lean/BusyBeaver/ZFC/ArithmeticHistoryRecurrence254.lean)
proves recurrence laws for the existing twelve-rule proof checker at every
internal index in an IΣ1 model. It imports the unchanged
[`ArithmeticHistory254`](arithmetic_history254.md) evaluator and introduces no
second validity computation.

The first theorem identifies each earlier history entry with its own result:

```text
i ≤ code → znth(history(code), i) = value(i).
```

The quantifier over earlier indices is bounded. The proof therefore uses
internal Σ1 induction, and applies when `code` or `i` is nonstandard. Exterior
lookups are separately proved to be zero.

For a positive proof code `raw + 1`, let `tag = raw % 12`,
`payload = raw / 12`, and `tail = second(payload)`. The successor theorem
rewrites the stored row in terms of actual child values. MP uses the codes
`first(tail)` and `second(tail)`; GEN uses the whole `tail`. Division and
Cantor projection bounds place every child at most `raw`, strictly below the
parent code, so these lookups are in range.

The resulting validity consequences retain the existing rules exactly:

- An accepted MP parent satisfies the original `MPGate`, including its
  predecessor witnesses and implication equation, and both child values are
  nonzero.
- An accepted GEN parent has a nonzero value at its whole-tail child code.

Here zero means invalid, while a valid proof of formula 0 has value 1.
Neither the truth alias nor a freshness gate is changed.

This is the validity interface needed by the planned compiler. Its raw-word
history can ignore validity during construction, with the existing checker
used once to return empty word 0 for invalid public inputs. At an accepted
parent, the new lemmas justify using the accepted-child execution hypotheses.
The [word history](arithmetic_proof_word254.md) now supplies this data
construction; its execution theorem remains separate work.

The [verification record](results/arithmetic-history-recurrence254-verification.json)
and [independent review](results/arithmetic-history-recurrence254-review.json)
record eleven axiom reports and twelve generic callers. All use only standard
Lean axioms. The narrow check reuses the five verified arithmetic modules and
twelve matched core modules; it freshly checks this extension and its audit.
No project umbrella or external dependency cache is rebuilt.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_history_recurrence254.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/dependency-checkout \
  --history-evidence /outside/successful-arithmetic-history/verification.json \
  --core-evidence /outside/successful-169-unit-core/verification.json \
  --output /outside/new-empty-history-recurrence-check
```

The runner checks the actual dependency objects selected by its library path
against the earlier evidence. Relocated matching caches can be supplied with
`--history-cache` and `--core-cache`. These recurrence laws do not prove the
compiler's execution contract or the internal PA consistency equivalence.
