import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.Taylor.GaussianGammaShiftedDeflatedPolynomial
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaEncodingRescaling
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaInputProperness
import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianProductNorm

/-!
# Exact zero-input behavior of the original deflated full polynomials

The native norm-zero case has deflated polynomial value exactly one at
every original query and cutoff. The same original shifted C7 name is
the original encoded-one name. These are arithmetic source proofs, not
a zero test on an arbitrary regular named input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaShiftedDeflatedZero

open_ipra
open GaussianGammaShiftedDeflatedPolynomial (rawValue)
open GaussianGammaOriginalC19Prefix (buffer totalDegree stage)
open GaussianGammaCanonicalExponent (source constantF)
open GaussianRationalHorner (ofGaussian qzero hornerF)
open GaussianRationalSyntheticDivision (qone qadd_congr)
open GaussianRootAlgebra (equal equal_of_values)
open ComplexLogarithmRemainder (zeroCode oneCode scale normSq)
open GaussianNameEquivalence (crossEquivalent cross_trans)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem zero_native (z : PTm n) (hz : Γ ⊢[PRAAx] normSq z ≐ zero) : Γ ⊢[PRAAx] equal z zeroCode := by
  have values := GaussianProductNorm.norm_zero_values z hz
  apply equal_of_values
  · simpa only [GaussianRootAlgebra.re_zero] using values.1
  · simpa only [GaussianRootAlgebra.im_zero] using values.2

theorem zero_fraction (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] normSq z ≐ zero) : Γ ⊢[PRAAx]
    ofGaussian z B ≐ qzero :=
  (GaussianGammaFiniteValueProperness.fraction_equal z zeroCode B hB (zero_native z hz)).eqTrans
    (GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalHorner.ofGaussian_canonical _ _ hB)
      GaussianRationalSyntheticDivision.qzero_canonical hB (GaussianRationalHorner.ofGaussian_represents _ _ hB)
      (GaussianRationalHorner.zero_represents B))

/-- The actual prefix removes only the original zero constant coefficient. -/
theorem raw_value_zero (q z R B d : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] normSq z ≐ zero) : Γ ⊢[PRAAx] rawValue q z R B d ≐ qone := by
  let L := GaussianGammaCofinalCoefficientName.degreeCutoff (stage q (succ d)) (two*R)
  let K := GaussianGammaCofinalCoefficientName.exponentialCutoff (stage q (succ d)) (two*R)
  let s := GaussianGammaCofinalCoefficientName.coefficientPrecision (stage q (succ d)) (two*R)
  let V := two*(two*R)+K*GaussianGammaReciprocalDegreeCells.degree L
  let C := buffer q R (succ d)
  have positive : Γ ⊢[PRAAx] le one K := le_trans (zero_lt_succ d)
    (le_trans (le_add_left (succ d) q) (GaussianGammaCofinalCoefficientName.exponential_cutoff_cofinal (stage q (succ d)) (two*R)))
  have shape : Γ ⊢[PRAAx] totalDegree q R (succ d) ≐ succ V := by
    dsimp only [totalDegree,GaussianGammaFiniteCoefficientPolynomial.totalDegree,V,K,L]
    ipra_ring
  have index : Γ ⊢[PRAAx] PTm.monus (totalDegree q R (succ d)) one ≐ V :=
    (congrMonus shape (.eqRefl _)).eqTrans ((succ_monus_succ V zero).eqTrans (monus_zero V))
  have linear : Γ ⊢[PRAAx] Foundations.MasterCertificate.entry C V ≐ qone :=
    (Foundations.SequenceComposition.entry_congr (.eqRefl C) index.eqSymm).eqTrans
      (GaussianGammaPolynomialConstantLinear.whole_linear s (two*R) L K positive)
  exact (congrAp3 hornerF shape (.eqRefl C) (zero_fraction z B hB hz)).eqTrans
    ((GaussianRationalHorner.horner_succ C qzero V).eqTrans
      ((qadd_congr (GaussianRationalSyntheticDivision.qmul_zero_right _) linear).eqTrans
        (GaussianRationalSyntheticDivision.qzero_add qone GaussianRationalSyntheticDivision.qone_canonical)))

theorem shifted_native (z B : PTm n) (hz : Γ ⊢[PRAAx] normSq z ≐ zero) : Γ ⊢[PRAAx]
    equal (GaussianGammaShiftTrajectory.point z B one) (scale B oneCode) := by
  have values := GaussianProductNorm.norm_zero_values z hz
  apply GaussianRootAlgebra.equal_trans (GaussianGammaShiftTrajectory.point_native z B one)
  apply equal_of_values
  · simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
    ipra_simps
    linear_combination values.1
  · simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one]
    linear_combination values.2

theorem original_shifted_one (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hz : Γ ⊢[PRAAx] normSq z ≐ zero) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF constantF (GaussianGammaRepeatedShift.stageData z R B one) qone :=
  cross_trans _ _ _ _ _ _
    (GaussianGammaInputProperness.original_C7_proper _ _ _ _ (GaussianGammaShiftTrajectory.point_source z R B one h) (shifted_native z B hz))
    (GaussianGammaEncodingRescaling.original_encoded_one_constant (R+one) B (le_trans h.andE₁ (le_add_right _ _)) h.andE₂.andE₁)

theorem actual_original_deflated_full_polynomial_at_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 3) ⋏ normSq (var 1) ≐ zero) ⟶ rawValue (var 0) (var 1) (var 2) (var 3) (var 4) ≐ qone) :=
  closeUniv 5 (.impI (raw_value_zero _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_original_zero_shift_is_original_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((source (var 0) (var 1) (var 2) ⋏ normSq (var 0) ≐ zero) ⟶
      crossEquivalent GaussianGammaC7Name.nameF constantF (GaussianGammaRepeatedShift.stageData (var 0) (var 1) (var 2) one) qone) :=
  closeUniv 3 (.impI (original_shifted_one _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaShiftedDeflatedZero
