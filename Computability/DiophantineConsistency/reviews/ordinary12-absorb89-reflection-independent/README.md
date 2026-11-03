# Absorbed-witness negative reflection

The 89-row graph differs from the 90-row graph by absorbing the old `r+s`
into one positive witness. Its absorbed witness appears only in the first
residual; the main and ordinary residuals do not depend on that witness.

`Absorb89FullReflection.output_invariant` was checked by Lean in
`observations/attempt01/`. In any commutative ring, if the unsquared first
residual equals `−b*first`, updating witness 7 by `+2*first` leaves the
*entire actual 89-row graph output* unchanged. The proof separately checks
the first, main, and ordinary residuals. Its printed axioms are `propext` and
`Quot.sound`. This result is conditional and is not an 89-row equivalence or
an iPRA proof.

`Absorb89ModelReflection.negative_branch_preserves` connects the natural-model
negative branch and transport bound to the ring hypothesis, then transfers the
invariant back to `InternalZero`. In every IΣ₁ model it assumes the actual
89-row output is zero, the bound `Bn < Bp`, and the negative branch equation
`b*(ell+k+r)+b*first=(1+k*b)*Bt`; it concludes that the output is still zero
after updating the absorbed witness to `r+2*first`. Here `Bt=q*(Bp-Bn)` and
the source spells out all abbreviations. These are exactly the relevant
conditions supplied by the earlier transport and signed-branch results. It
does not by itself prove that a positive zero exists after subtracting `s`,
or establish the positive-sign branch or full equivalence.

The first model compilation attempt is retained in
`observations/model-attempt01/` and failed on elaboration; the revised source
passed with empty stderr in `observations/model-attempt02/`. Its object SHA-256
is `5f65eb40986de1bb580103f8c9b5682cbd12b7f4e4b40643c7e473f885559a55`,
and its printed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Both successful checks rehashed the selected 1,291-file union. Package,
dynamic, and historical source-to-object ancestry remain inherited. The model
reflection source locally disables the unused-simp-argument linter, so that
class of warning was not checked there.
