# Independent review of positive 87/36 ↔ 88/30 auxiliary draft

No source-level mathematical mismatch was found in the inspected graph rows,
strict-bound cut, generic auxiliary interface, or direction of the two
proposed maps. This does not establish Lean elaboration, provider or axiom
compatibility, or that either graph supplies `BoundsCut`.

Both graph literals have the same input order except coordinate 11, which is
`y` for 87 and `u` for 88. Their first, main, strong, `Q`, and signed `z`
fields exclude coordinate 11. The 87 auxiliary field is
`y²−Q*(y²−z²)−1`; the 88 field is
`(z+u)²−Q*u*((z+u)+z)−1`. The reviewed `z` and `Q` formulas match their
literal graph dependencies, including the signed rank and actual X/Y inputs.
The four graph squares match the proposed five-square interface with its
fifth argument zero.

The generic `positive_aux_coordinate_iff` has **old u on its left** and
**direct positive y on its right**. Accordingly, the 87→88 step uses `.mpr`
and the 88→87 step uses `.mp`. Each keeps the same non-auxiliary valuation,
port tuple, signed z, and Q; the helper produces the replacement as a
positive natural in the same model. It assumes `1<Q` and `1<z²`, not
positivity of z. The draft's `BoundsCut` requires those inequalities for a
positive zero of either actual graph, and the generic helper's assumptions
match that cut exactly. This review does not prove the cut.

The receipt pins the exact graph/source bytes, checks all literal row strings
and coordinate dependencies, checks the witness-interface directions, and
exercises bounded scalar auxiliary witnesses including negative z. Those
controls are not graph zeros or all-model proofs. Reproduce from
`Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-positive87-to88-aux-map-independent/check.py
```
