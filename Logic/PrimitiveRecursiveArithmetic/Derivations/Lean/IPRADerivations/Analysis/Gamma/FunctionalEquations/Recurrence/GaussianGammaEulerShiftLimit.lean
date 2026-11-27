import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianGammaEulerShift
import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaEulerConvergence
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalLinearProduct

/-!
# The actual coefficient in the original finite Euler shift

The actual exponential/data in the finite shift are preserved. The
mesh-log inverse identity is an explicit local input until its separate
supplier is combined. All finite products use multiplication, including
zeros of the Euler head. The finite-to-C7 limit is a separate consumer.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerShiftLimit

open_ipra
open GaussianGammaEulerHeadShift (shifted linear)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (qF qData q_regular)
open GaussianGammaEulerShift (expF negativeLogExpData negative_log_exp_regular leftF leftData rightF rightData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianRationalHorner (ofGaussian qmul positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def reciprocalPoint (N : PTm n) : PTm n := ofGaussian ComplexLogarithmRemainder.oneCode N
def logInverse (N : PTm n) : Fm PTm n :=
  crossEquivalent expF constantF (negativeLogExpData N) (reciprocalPoint N)
def correction (z B N : PTm n) : PTm n := qmul (linear z B (succ N)) (reciprocalPoint N)
def correctedF : PR 2 := multiplyF constantF qF
def correctedData (z B N : PTm n) : PTm n := multiplyData constantF qF (correction z B N) (qData z B N)
ipra_subst reciprocalPoint
ipra_subst logInverse [negativeLogExpData, GaussianGammaEulerShift.negativeLogData, GaussianGammaFiniteApproximantName.exponentialInputData]
ipra_subst correction
@[simp] theorem subst_correctedData {l : ℕ} (σ : Fin n → PTm l) (z B N : PTm n) :
    Syn.subst σ (correctedData z B N) = correctedData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [correctedData,qData,GaussianGammaFiniteApproximantName.approximantData,
    GaussianGammaFiniteApproximantName.exponentialInputData]
  have h := GaussianGammaCutoffName.subst_head σ z B N
  simp only [GaussianGammaCutoffName.head] at h
  rw [h]

theorem finite_shift_reciprocal (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] logInverse N) : Γ ⊢[PRAAx]
    crossEquivalent leftF correctedF (leftData z B N) (correctedData z B N) := by
  let Q := qData z B N
  let E := negativeLogExpData N
  let u := reciprocalPoint N
  let c := linear z B (succ N)
  have qn := q_regular (Γ := Γ) z B N hN
  have en := negative_log_exp_regular (Γ := Γ) N hN
  have un := constant_regular (Γ := Γ) u
  have cn := constant_regular (Γ := Γ) c
  have inner := multiply_cross qF qF expF constantF Q Q E u qn qn en un (cross_refl _ _ qn) hi
  have replace := multiply_cross constantF constantF (multiplyF qF expF) (multiplyF qF constantF)
    c c (multiplyData qF expF Q E) (multiplyData qF constantF Q u) cn cn
    (multiply_fast qF expF Q E qn en) (multiply_fast qF constantF Q u qn un) (cross_refl _ _ cn) inner
  have swap := GaussianNameRingLaws.multiply_commutative qF constantF Q u qn un
  have exchange := multiply_cross constantF constantF (multiplyF qF constantF) (multiplyF constantF qF)
    c c (multiplyData qF constantF Q u) (multiplyData constantF qF u Q) cn cn
    (multiply_fast qF constantF Q u qn un) (multiply_fast constantF qF u Q un qn) (cross_refl _ _ cn) swap
  have merge := GaussianGammaEulerShift.merge_head qF c u Q qn
  exact cross_trans _ _ _ _ _ _ (GaussianGammaEulerShift.finite_shift z B N hB hN)
    (cross_trans _ _ _ _ _ _ replace (cross_trans _ _ _ _ _ _ exchange merge))


theorem shifted_bound (z R B : PTm n)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded (shifted z B) ((R+one)*B) := by
  have unity : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (ComplexLogarithmRemainder.oneCode : PTm n) one :=
    le_congr ComplexLogarithmRemainder.normSq_one.eqSymm (by ipra_ring) (le_refl one)
  have h := ComplexLogarithmRemainder.bounded_add hz (ComplexLogarithmRemainder.bounded_scale B unity)
  apply le_congr (b' := ((R+one)*B)*((R+one)*B)) ?_ (by ipra_ring) h
  apply deriveNat
  rw [ComplexLogarithmRemainder.normSq_eval,ComplexLogarithmRemainder.normSq_eval]
  simp only [shifted,GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
    GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  ipra_simps
  ring

theorem shifted_source (z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) : Γ ⊢[PRAAx]
    GaussianGammaCanonicalExponent.source (shifted z B) (R+one) B :=
  .andI (le_trans h.andE₁ (le_add_right R one)) (.andI h.andE₂.andE₁ (shifted_bound z R B h.andE₂.andE₂))

theorem correction_represents (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.represents (correction z B N) (GaussianGammaEulerHeadLower.translated z B (succ N)) (B*N) := by
  have h := GaussianRationalHorner.qmul_represents (Γ := Γ) (linear z B (succ N)) (reciprocalPoint N)
    (GaussianGammaEulerHeadLower.translated z B (succ N)) ComplexLogarithmRemainder.oneCode B N hB hN
    (GaussianRationalHorner.ofGaussian_represents _ _ hB) (GaussianRationalHorner.ofGaussian_represents _ _ hN)
  apply GaussianRationalHorner.represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := h)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ring

theorem correction_difference_represents (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.represents (GaussianRationalMetric.qsub (correction z B N) GaussianRationalSyntheticDivision.qone)
      (shifted z B) (B*N) := by
  have h := GaussianRationalMetric.qsub_represents _ _ _ _ _ (positive_product _ _ hB hN)
    (correction_represents z B N hB hN) (GaussianRationalReciprocal.qone_represents_scaled (B*N))
  apply GaussianRationalHorner.represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := h)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,GaussianGammaEulerHeadLower.translated,shifted,
      GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add] <;> (try ipra_simps) <;> ring

/-- The actual rational finite shift coefficient is 1+(z/B+1)/N in
field value, with exact Euclidean error (R+1)/N. -/
theorem correction_distance (z R B N : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (correction z B N) GaussianRationalSyntheticDivision.qone (R+one) N := by
  have hz := shifted_bound z R B h.andE₂.andE₂
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ (positive_product _ _ h.andE₂.andE₁ hN) hN
    (correction_difference_represents z B N h.andE₂.andE₁ hN)
  exact le_congr (.eqRefl _) (by ipra_ring)
    (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (N*N)) hz)

theorem correction_bound (z R B N : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (correction z B N) (R+two) one := by
  have combined := GaussianRationalReciprocal.bounded_sum _ _ one one (R+one) N (le_refl one) hN
    GaussianRationalReciprocal.qone_bounded (correction_distance z R B N h hN)
  have value := GaussianRationalLinearProduct.add_sub_right (Γ := Γ) GaussianRationalSyntheticDivision.qone (correction z B N)
    (GaussianRationalHorner.qmul_canonical _ _)
  have clear : Γ ⊢[PRAAx] le ((one*N+(R+one)*one)*one) ((R+two)*(one*N)) := by
    ipra_le (Groth.ι (IPRA.Q.mk Γ R)+1)*sl hN
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_refl one) hN) (le_refl one) clear
    (GaussianRationalReciprocal.bound_congr value (.eqRefl _) (.eqRefl _) combined)


theorem original_finite_shift_log_inverse_adapter_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (var 2) ⟶ logInverse (var 2) ⟶
      crossEquivalent leftF correctedF (leftData (var 0) (var 1) (var 2)) (correctedData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (finite_shift_reciprocal _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem original_shifted_disk_source_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶
      GaussianGammaCanonicalExponent.source (shifted (var 0) (var 2)) (var 1+one) (var 2)) :=
  closeUniv 3 (.impI (shifted_source _ _ _ Prf.hyp0))

theorem original_finite_shift_coefficient_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶ le one (var 3) ⟶
      GaussianRationalMetric.distanceBounded (correction (var 0) (var 2) (var 3)) GaussianRationalSyntheticDivision.qone
        (var 1+one) (var 3)) :=
  closeUniv 4 (.impI (.impI (correction_distance _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_finite_shift_coefficient_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶ le one (var 3) ⟶
      GaussianRationalMetric.bounded (correction (var 0) (var 2) (var 3)) (var 1+two) one) :=
  closeUniv 4 (.impI (.impI (correction_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerShiftLimit
