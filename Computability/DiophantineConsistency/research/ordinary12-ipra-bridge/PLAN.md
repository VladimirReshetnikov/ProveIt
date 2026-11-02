# Concrete proof plan and dependency boundary

The target literal is `ordinary-unit-products/p12_ordinary_degree70.json`,
SHA-256 `444c25b68fbfee600ae174cb5bad1931897a55ffe2f9570fd22f3281f6e97010`:
12 positive coordinates, 100 live binary operations, and the ordinary
certificate's degree 70. Its exact source, ordinary derivation and relevant
historical module hashes are pinned in `source-pins.json`. Hashes and finite
tests do not prove the derivation.

**Port prerequisite.** The fixed compact44 `β=2^590069−1` differs from the
2011 endpoint's `β=2^94517−1`; the remaining three fixed ports must also be
bound as one complete tuple. First construct and verify the exact 12-variable
literal and positive shift over that tuple. Separately establish the needed
native checker/calibration for these particular ports. The old fixed 2011
endpoint is not a substitute, and model-uniform carrier lemmas may be used
only after their hypotheses are checked for the compact44 tuple.

**Residual split, precise target.** Let `A0`, `A1`, `N`, `bn` be the
candidate's exact literal subexpressions and `P=(1+A0)(1+A1)(1+N)-1`.
For every intended arithmetic model and positive valuation prove
`P=0 → A0=0 ∧ A1=0 ∧ N=0`, with signed expressions represented by the
repository's formal-difference pairs. One concrete route is:

1. Prove a 100-row literal-to-scalar identity and establish the exact three
   factors as signed pairs, without cancellation of nonunits or a hidden
   positivity assumption.
2. For `q=1+β(6j+1)`, prove `q` even from the compact44 parity facts. Hence
   `M=q³(q−1)` and `U=q²Y` are even. Independently prove
   `bn=2(1−Q)(n+V)` even. The six compiled finite `ZMod 4` lemmas cover
   the corresponding residue exclusions only; lift them through the signed
   pair residue map, including the exact associativity of `d·bn²·Q`.
3. From the three-factor product being one, derive magnitude one for each
   factor, then exclude `−1` and conclude each factor is `+1`. The pinned
   `ArithmeticSignedPairs.magnitude_multiply` and `product5_magnitudes`
   may support a three-factor proof by padding with units; the pinned
   `ArithmeticAdaptiveFactorUnits2011.pairEval_residue` and
   `negative_residue` provide a candidate residue bridge. Their current
   declarations assume an `IΣ₁` model and concern different literals;
   applicability to this exact graph and the desired object theory must be
   proved, not inferred from matching names.

**Early rank before norm recovery.** With only `A0=A1=0` and the explicit
positive/port hypotheses, construct internal witnesses for the divisions
and Pell indices, proving successively `q³∣Y`, `q−1∣Bt`, `C>0`, the scalar
window `3q<R<q⁴−2`, positivity of `Dstar`, and `q⁴∣v` where `v=k−R−1` is
represented without unjustified natural subtraction. Prove the first and
main Pell index statements and their recurrence congruence, then derive
`p>m1≥24`, `c>(a+2)Δ²`, `c>2R`, and `V>c>1`. The pinned
`ArithmeticPellClassification`, `ArithmeticPellFirstNorm`, recurrence,
divisibility and `ArithmeticAdaptiveRankWindow2011.scalar_rank_window`
are candidates for reuse, subject to exact hypotheses. In particular,
`ArithmeticPellFirstIndex.first_main_indices` already assumes a strong norm
and auxiliary norm; invoking it to prove the *early* bounds before recovering
those norms would be circular.

**Ordinary norm elimination and transport.** From `N=0`, `Q>1`, `bn≠0`
and the early bounds, formalize the adjacent-coefficient rational-integrality
descent inside the intended model. State the signed divisibility explicitly:
obtain an integral signed `i0` satisfying `d·bn·i0=AN`, then obtain the
auxiliary witness and the ordinary strong equation `(ic²)²=Δ(f²−1)`.
Do not assume `Δ∣i`. The pinned
`ArithmeticPellIntegralSolution.integral_solution_tsub`,
`ArithmeticPellIndexDivisibility`, and `ArithmeticPellResidueAux` cover
parts of the subsequent Pell recovery under their stated hypotheses; the
new graph-to-hypotheses bridge and early size estimates remain to be built.
Formalize the displayed ordinary maps in both directions and check every
positivity/divisibility obligation rather than treating rational quotients as
internal integers automatically.

**Object-level conclusion.** An external Lean proof over `ℕ` or an `IΣ₁`
model is not by itself a proof that the required formula is provable in
iPRA. Use a fully specified syntactic bridge for the exact new formula and
the compact44 checker. The pinned `IPRAFullGGTransfer.from_classical` is a
candidate only after supplying its required classical PRA derivation and
checking the translated target; its source explicitly leaves identification
of the translated and chosen native consistency predicates separate. A
matched project replay and independent artifact audit must then check both
directions and the final axiom reports.

**Provider discipline.** Build only against an authenticated historical
parent and separately authenticated fresh sibling seeds; freeze new source
and check actual compiler dependencies and terminal exits. Do not mix the
recently merged `ModelArithmetic`, `ModelCarrierCurrent`,
`ModelCarrierScaled`, `ModelDifferenceRing` or `DiscreteOrderedRingFacts`
objects into that parent: those modules are not in its 1,210-row manifest.
They require a coherent source-current successor closure if used. Disk was
near the existing reserve during this assessment, so no large rebuild was
started.
