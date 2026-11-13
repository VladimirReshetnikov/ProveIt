# Uncompiled conditional 38-seed assembly

`SharingNormCompose.lean` (SHA-256 `d1758d81480e229305c6da73ccde257440242cb1cff92748814851ea6e08eb8f`) drafts how the externally audited 38-witness seed would connect to the existing 14-variable current equation in every IΣ₁ model. This is a separate prospective stage; it is **not** in the frozen six-stage check sequence. No Lean process has parsed or checked this file.

`naturalPorts` specifies β, K, the low mask and the high mask plus β, in that order. `inputPrefix` takes the first fourteen of the thirty-eight seed witnesses. The condition `unitNorms u` is the conjunction of the five original `Carrier65` unit norms evaluated at `ι(u+1)` and the current difference-ring ports. The candidate theorem `current_zero_iff_unitNorms` attempts to reuse the checked `FreshModel106.evalRing_expressionAt65`, `FreshCarrierSpheres.value65_zero_iff_norms`, `modelFacts`, beta positivity and positivity of the shifted model coordinates. This theorem and its imports, rewriting and inference have not been checked here.

The core result is explicitly **conditional** on two declarations whose proofs are absent:

* `Extraction`: every zero of the seed gives the five unit norms at the input prefix. This needs zero extraction from the sum of squares in the model difference ring, source-to-static assignment correspondence and the complete topological residual-to-ring induction, including positivity and cancellation of Δ in the scaled strong norm.
* `Construction`: the proposed semiring witness constructor gives a seed zero whenever the five original unit norms hold. This needs exact natural-to-difference-ring identities for all four ports, evaluation of every generated cut/residual and the terminal norm identities.

`existential_seed_iff_current` is only the proposed composition of these assumptions with the original norm theorem, not an unconditional proof. Neither Jones normalization/degree nor the resulting nine-variable expression nor an iPRA endpoint follows from the present draft. The 38-seed syntax, constructor, static-assignment and generic model drafts imported or referred to by this route also remain uncompiled pending their separately coordinated checks. The provider chain used by the earlier carrier prelude must be resolved and guarded for any later compile; this file has not been included in any prepared runner.
