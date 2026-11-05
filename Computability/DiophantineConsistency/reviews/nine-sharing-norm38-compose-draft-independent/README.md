# Independent source review of the norm38 composition draft

The pinned uncompiled source proposes an equivalence between existence of a
38-coordinate seed zero and existence of a 14-coordinate zero of the shifted
current expression. Its logical assembly is correct **assuming both stated
obligations and the proposed current-zero/unit-norm equivalence**:
`Extraction` turns each seed zero into the five norms at its input prefix;
`Construction` turns those norms into a seed zero using the proposed forward
constructor. The conditional theorem uses each assumption in the corresponding
direction and does not infer either assumption from the other.

The five norm fields agree in order with the referenced
`FreshCarrierSpheres.value65_zero_iff_norms`: P, Q, U, strong and W. The
positive shift is applied as `ι(u j + 1)`. The 14-element prefix of `Fin 38`
corresponds to the first 14 witnesses after the distinguished seed input;
`Fin.cons 1 w` supplies input 1, matching the interface of
`NineFreshJones.nine_iff`. The natural port order is beta, K, low mask, high
mask plus beta **once**. The pinned prelude source contains matching `port0`
through `port3` statements, but their exact compiled provider routing must be
verified in any build. No mathematical falsehood was identified in the stated
conditional equivalence.

`check.py` pins the reviewed source texts and checks selected statement
fragments; it is not a Lean parser or proof. In particular, the proposed
rewriting and inferred typeclass arguments in `current_zero_iff_unitNorms`,
the imported providers, all extraction/construction proofs, Jones degree and
normalization, and the iPRA endpoint remain unchecked. This draft is not part
of the separate six-stage check sequence. No Lean process was run.
