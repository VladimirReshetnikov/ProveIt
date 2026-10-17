# A represented checker with PA-provable totality

[ArithmeticHistory254.lean](../../Lean/BusyBeaver/ZFC/ArithmeticHistory254.lean)
completes the arithmetic representation of the existing twelve-rule C254
checker. It supplies fixed parameter-free formulas for its history, output and
Boolean result, proves their totality in every IΣ1 model, and identifies their
standard interpretation with `Code254Proof.check` on every input. It also proves
an actual PA derivability theorem for the fixed sentence asserting unique
Boolean evaluation. The PA proof relating machine traces to ZFC refutations
remains a separate obligation.

The construction retains the exact original calculus and coding, attributed to
Mira-Cult and Jeff through the [imported baseline](../../../../lib/jeff-busy-beaver-zfc254/README.proveit.md).
It builds on the [complete arithmetic row](arithmetic_row254.md). For positive
code `c`, the represented selector uses `(c−1)%12` and `(c−1)/12`, decodes the
literal Cantor payload, and obtains the actual child results from a represented
sequence. Code zero returns zero. A valid proof of formula zero has value one;
invalid proofs have value zero.

One fixed `PR.Blueprint 0` starts with the sequence `[0]` and appends the value
for code `i+1` at step `i`. Foundation's represented iteration proves that its
result exists uniquely at every internal index. The additional `history_seq`
and `history_length` theorems use definable IΣ1 induction, so they cover
nonstandard indices as well as ordinary natural numbers. No arbitrary function
or child-result oracle appears in the final formula. Foundation's own pairing
encodes the auxiliary sequence; the earlier literal Cantor adapter still
decodes the proof payload.

The interfaces are:

| Declaration | Checked statement |
| --- | --- |
| `history_defined`, `history_defined_delta` | Fixed Σ1 and Δ1 graphs of the complete history function. |
| `value_defined`, `value_defined_delta` | Fixed graphs of the lookup at the requested code. |
| `checkValue_defined`, `checkValue_defined_delta` | Fixed graphs of the Boolean checker, including rejection. |
| `history_total`, `value_total`, `checkValue_total` | Unique outputs at every element of every IΣ1 model. |
| `history_lookup_nat` | Agreement with the existing list history for every history length and every lookup index, including out-of-range zero. |
| `checkDef_nat`, `checkValue_nat` | Agreement with the actual `Code254Proof.check` for all codes and conclusions, including malformed inputs. |
| `c254_iff_represented` | Ordinary C254 derivability iff some natural code satisfies this same fixed acceptance formula. |
| `isigma1_proves_totality`, `peano_proves_totality` | Actual arithmetic derivations of `totalitySentence` in IΣ1 and PA. |

The last sentence says that for every code and requested conclusion there is
exactly one Boolean result satisfying `checkValueDef`. Arithmetic completeness
is applied only after proving this statement in **every** IΣ1 model. This use
does not infer an internal theorem from behavior on standard quotations alone.
The standard-model comparison separately checks Foundation's division and
remainder against the usual natural operations, including divisor zero.

The [maintained verification](results/arithmetic-history254-verification.json)
freshly checks all five arithmetic modules and their stored audits:
**151 named axiom probes and 164 callers**. This module contributes 37 probes
and 44 callers. Its source check took 9.685 seconds, its audit 3.128 seconds,
and the four-module prerequisite check 48.893 seconds. The source and audit
emitted no warnings. The
[independent review](results/arithmetic-history254-review.json) covers the
internal iteration, all-input comparison, arithmetic totality sentence and
runner. Verification records the exact source and cached-object identities;
the only permitted Lean axioms are `propext`, `Classical.choice` and `Quot.sound`.

This is the separate Foundation/Mathlib lane, outside the 167-unit Std-only
runner. Use the same pinned, already built dependencies and matching core cache
as the preceding arithmetic adapters:

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_history254.py \
  --dependency-root /path/to/built/dependency/checkout \
  --core-evidence Computability/BusyBeaver/Research/ZFC/results/binary-zfc252-integration-verification.json \
  --core-cache /path/to/matching/core/cache
```

The next PA obligations are represented translations between accepted C254,
native-theory, ZF and ZFC refutations, and the comparison with finite traces of
the actual 252-state binary machine. Those require correctness on all internal
codes. The external Lean nonhalting/Con(ZFC) equivalence is already checked;
checker totality alone does not internalize that equivalence or reduce the
machine's state count.
