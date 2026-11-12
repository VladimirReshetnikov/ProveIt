# Proposed positive-difference model transfer: 37 to 38 variables

This packet proposes Lean source for the corrected
[37-variable quartic](../adaptive-square-sums37-difference-quartic/README.md),
at the exact candidate SHA-256 pinned by `generate.py`. It builds on the
separate, unelaborated [38-variable model draft](../adaptive-qm38-conditional-model-draft/README.md),
which in turn targets the historical current-port 40-variable endpoint. This is
not the separate natural-79 compact-port equation. **No Lean command or axiom
report has run**, and the proposed endpoint remains conditional on explicit
37- and 38-variable graph/model obligations.

The generated positive-domain literal has 37 variables and 158 arithmetic
rows; its named 28-residual sum has been checked externally as an exact DAG.
The candidate's separate natural-shift encoding is reported as 195 rows.
`AdaptiveQM38ResidualZeros` and `AdaptiveQM37ResidualZeros` propose the usual
sum-of-squares zero iff all residuals vanish, following the existing
`AdaptiveQM40Zeros.new_all` source pattern.

`AdaptiveQM37DifferenceWitness` proposes the new substantive model argument.
For a positive 38-variable zero, parent residuals 4 and 21 identify the
stored `squareVariable` and `ySquareVariable` with `v²` and `y²`. Parent
auxiliary residual 2 yields, in the natural model after the difference-ring
calculation,

```text
Q*y² + 1 = Q*v² + y².
```

The named Q and y coordinates are positive. If `y² < v²`, multiplication by
positive Q and `1 ≤ y²` make the left side strictly smaller than the right,
a contradiction. Thus `v² ≤ y²`, so the model's ordered-semiring witness
property supplies `d` with `y²=v²+d`; projection stores `d+1`, which is
positive. This avoids assuming that subtraction in the natural model is ring
subtraction. Every step, including residual reduction, casts, `linear_combination`
and the witness extraction, is an untested source proof.

The proposed coordinate maps project old slot 13 to `d+1` and omit old slot
30; extension restores those slots as `v²` and `y²`. Positivity and shifted
no-zero transfer are drafted. The crucial graph-zero implications remain
explicit `GraphZeroObligations`, and the final conditional native/standard
clients also require the earlier 38↔40 obligations. The separate
[residual-map draft](../adaptive-qm37-residual-maps-draft/README.md) proposes
actual proofs of those graph obligations; it remains unelaborated too. This
modular boundary permits a later 36-variable transfer to compose above the
37-variable literal without silently assuming either map.

`check_source.py` pins the corrected 37 and 38 graphs and these source files,
checks their variables and residual indices, and exercises 100 positive finite
lift/project controls. The separate author's checker proves its stated exact
external residual-polynomial identities; neither check proves a Lean or
all-model theorem. Physical TeX/PDF binding, complete provider provenance,
axioms and proof-resource behavior remain separate.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-qm37-conditional-model-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/adaptive-qm37-conditional-model-draft/result.json
```

`generate.py` regenerates only the literal, residual source and observation in
this packet; it does not invoke Lean.
