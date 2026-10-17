# A bounded arithmetic graph for the complete C254 rule row

[ArithmeticRow254.lean](../../Lean/BusyBeaver/ZFC/ArithmeticRow254.lean)
represents the full twelve-case rule step by one fixed, parameter-free bounded
formula. It extends the [positive templates](arithmetic_templates254.md) with
truth, MP, GEN, both bundle freshness gates, and rejection of every unknown
tag. The result is proved in every model of open induction (IOpen), including
nonstandard inputs. This remains one component of the requested PA proof.

`rowDef` has five free slots: result, rule tag, payload and two already supplied
child results. `row_defined` proves that it is exactly the graph of
`rowKernel`. A child result is zero when invalid and one plus its formula code
when valid, matching the existing history checker. The underlying calculus and
fixed templates retain Mira-Cult's and Jeff's attribution through the
[imported baseline](../../../../lib/jeff-busy-beaver-zfc254/README.proveit.md).

Witness bounds work even when the output is zero. Payload components are
bounded by the payload. The MP test bounds predecessor witnesses by the two
child results, so its negation can reject an invalid major premise without
trying to bound a large intermediate formula by zero. GEN and the positive
templates bound their formula witness by the successful output. The bundle's
two failed freshness cases return zero without requiring its positive formula
to fit beneath that zero. Tags outside 0 through 11 also return exactly zero.

`rowKernel_nat` identifies this function with the actual
`Code254History.row rec tag payload` for every natural tag and payload and
every supplied child-result function `rec`. `rowGraph_nat` gives the same
comparison directly for the fixed formula. The first supplied slot is GEN's
tail lookup or MP's minor lookup; the second is MP's major lookup. These
theorems do **not** represent the lookup operation or encode an arbitrary
function as a natural number. The subsequent [history extension](arithmetic_history254.md)
supplies the actual lookups, history construction, code-zero handling and
tag-modulo-12 decoding. Proof translation and finite machine traces remain
separate obligations.

The [maintained verification](results/arithmetic-row254-verification.json)
freshly checks Cantor, constructors, templates and this row, with all four
stored audits: **114 named axiom probes and 120 callers**. This module has
17 probes and 37 callers, including all twelve rule branches, failed MP,
both freshness collisions and invalid tags. Its source check took 17.219
seconds, its audit 2.779 seconds and the prerequisite checks 28.632 seconds.
The source emitted no warnings; only `propext`, `Classical.choice` and
`Quot.sound` occur. The [independent review](results/arithmetic-row254-review.json)
records the exact source and remaining boundaries.

This is a separate Foundation/Mathlib lane, outside the Std-only
runner. The maintained checker verifies the source and recorded object hashes
of the twelve reused core dependencies, including the actual
`Code254Proof` and `Code254History`; it neither builds nor downloads dependency
libraries. Reproduce using an existing clean built dependency checkout and
the recorded or relocated matching core cache:

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_row254.py \
  --dependency-root /path/to/built/dependency/checkout \
  --core-evidence Computability/BusyBeaver/Research/ZFC/results/binary-zfc252-integration-verification.json \
  --core-cache /path/to/matching/core/cache
```

The fixed Foundation pin and cache requirements are the same as the preceding
arithmetic adapters. No complete PA proof or new machine state count follows
from this row graph alone.
