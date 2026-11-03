# Independent absorbed-witness 89/90 equivalence review

`Absorb89Equivalence.positive_zero_iff` states that for every IΣ₁ model and
natural port tuple satisfying `0 < beta`, `MC < beta`, and `MF < 2*beta`,
the actual 89-row Lean graph has a strictly positive zero iff the actual
90-row Lean graph has one. The implication from 90 to 89 adds `s` to witness
7. In the other direction, `select` either keeps the witness in the positive
first-root branch or reflects it to a new positive full-graph zero in the
negative branch; the resulting absorbed witness exceeds `s`, so the inverse
map subtracts `s` and remains positive.

The independent audit checked the six-stage main/orientation/index/rank/
early/window chain, the growth and positive-branch results, and the forward,
selection, inverse, and final equivalence sources and receipts. It verified
the accepted source snapshots, output object hashes, logs and allowed axiom
reports, sampled resource guards, selected predecessor resolution, and the
1,291-file union twice. The first positive-branch and inverse attempts failed
and are preserved; the audit verifies they are not treated as accepted. The
external DAG checker confirms 89 live operations (50 multiplications,
22 additions, 17 subtractions) for the pinned graph.

The index theorem supplies first Pell index at least 13 only under the stated
bounded-port and positive-zero hypotheses. The positive-branch theorem also
requires the first norm, positive transport term and positive signed equation;
the selection proof obtains those from the earlier graph lemmas. The checked
result here is an existence equivalence in the specified IΣ₁ models. It is not
by itself a fixed-port halt theorem, an iPRA derivability theorem, or a formal
binding of any PDF. No independent Lean replay was made; full package,
dynamic, and historical source-to-object ancestry remain inherited.
