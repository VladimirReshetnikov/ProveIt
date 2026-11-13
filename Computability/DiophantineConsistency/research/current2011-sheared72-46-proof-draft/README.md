# Uncompiled 72/46 shear proof draft

`ShearDraft.lean` is a source draft only: **none of its declarations has been compiled or kernel checked**. It does not import or prove a literal candidate graph evaluator and does not assert an all-model zero bridge or iPRA endpoint. No Lean process was launched for it.

The draft isolates four proof components:

- `ordinary_strong_mod_c` extracts the proof-local residue argument from `ArithmeticCarrier94Indices.ordinary_half_index`. Its explicit hypotheses include positivity, the main Pell norm, the ordinary relaxed strong norm and the large-`c` bound. The argument uses `relaxed_auxiliary`, Pell index divisibility and the Pell identity; the ordinary strong norm alone is insufficient.
- `auxiliary_shear` states the exact commutative-ring identity for `y_old = V+y`.
- `positive_shear_of_unit_norm` states the order lemma that a unit auxiliary norm and `1 ≤ A`, `1 ≤ y`, plus `V ≠ 1`, force `y > V`.
- `shifted_ordinate_ne_zero` attempts to rule out `V+y=0` for a candidate zero, given explicit bounds `1 ≤ y`, `2 ≤ I`, and `A=0 ∨ 2 ≤ A`; `auxiliary_abs` records sign invariance. These order proofs are untested and may need refactoring or different hypotheses.

Still needed are a checked literal evaluator and shear identity tied to the fixed candidate graph; extraction of the parent 71/60 or 67/94 norm equalities and window bounds in arbitrary IΣ₁ models; the modular exclusion of `V=1` using the extracted residue, `8 ≤ R` and `2R<c`; construction of positive natural-coordinate witnesses in both directions, including the nonzero/absolute-value case; the final same-no-zero bridge and iPRA/GG transfers. The residue argument's proof-local dependencies and elaboration/resource behavior have not been tested. The graph and its external degree certificate are documented separately in `research/current2011-sheared72-46-candidate/`.
