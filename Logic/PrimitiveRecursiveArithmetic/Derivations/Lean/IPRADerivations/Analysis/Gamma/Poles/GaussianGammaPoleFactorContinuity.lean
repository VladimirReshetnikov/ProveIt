import IPRADerivations.Analysis.Gamma.Poles.GaussianGammaLocalPoleGuards
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameArithmetic
import IPRADerivations.Analysis.Gamma.Poles.GaussianGammaPoleFiniteFactors
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianApproximateInverseDistance

/-!
# Continuity of the actual finite correction factors at a Gamma pole

The original Euler-head product at -h/B is literally the product of
1-h/(B*k), k=1,...,j. Its distance to one is bounded by j*2^j*A/D
from the original Euclidean |h/B|<=A/D<=1. This is a finite ingredient
for C23, without an assumed derivative or named Gamma continuity law.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPoleFactorContinuity

open_ipra
open ComplexLogarithmRemainder (neg scale normSq)
open GaussianGammaEulerHead (factor product product_step)
open GaussianRationalHorner (ofGaussian qmul positive_product)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def input (h B A D : PTm n) : Fm PTm n := le one B ⋏ (le one D ⋏
  (le A D ⋏ ComplexLogarithmRemainder.bounded (scale D h) (A*B)))
def correction (h B j : PTm n) : PTm n := product (ComplexLogarithmRemainder.neg h) B j
def budget (A j : PTm n) : PTm n := A*j*unit j
ipra_subst input [ComplexLogarithmRemainder.bounded]
ipra_subst correction
ipra_subst budget

theorem factor_difference (h B i : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qsub (factor i (ComplexLogarithmRemainder.neg h) B) qone ≐ ofGaussian (ComplexLogarithmRemainder.neg h) (B*succ i) := by
  let E := B*succ i
  have hE := positive_product (Γ := Γ) _ _ hB (zero_lt_succ i)
  have raw := GaussianRationalMetric.qsub_represents (factor i (ComplexLogarithmRemainder.neg h) B) qone
    (GaussianGammaEulerHeadLower.translated (ComplexLogarithmRemainder.neg h) B (succ i)) (scale E ComplexLogarithmRemainder.oneCode) E hE
    (GaussianGammaEulerHeadLower.factor_represents i (ComplexLogarithmRemainder.neg h) B hB)
    (GaussianRationalReciprocal.qone_represents_scaled E)
  have same : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (GaussianRootAlgebra.sub (GaussianGammaEulerHeadLower.translated (ComplexLogarithmRemainder.neg h) B (succ i))
        (scale E ComplexLogarithmRemainder.oneCode)) (ComplexLogarithmRemainder.neg h) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
        GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
    all_goals (dsimp only [E]; ipra_simps; ring)
  exact GaussianRationalHorner.canonical_unique _ _ _ E (GaussianRationalMetric.qsub_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hE) hE
    (GaussianRationalHorner.represents_congr (.eqRefl _) same (.eqRefl _) raw)
    (GaussianRationalHorner.ofGaussian_represents _ _ hE)

theorem small_fraction_bound (h B A D i : PTm n) (hi : Γ ⊢[PRAAx] input h B A D) : Γ ⊢[PRAAx]
    bounded (ofGaussian (ComplexLogarithmRemainder.neg h) (B*succ i)) A D := by
  have hE := positive_product _ _ hi.andE₁ (zero_lt_succ i)
  apply (GaussianRationalMetric.bounded_iff _ _ _ _ _ hE hi.andE₂.andE₁
    (GaussianRationalHorner.ofGaussian_represents _ _ hE)).iffMpr
  have old := le_congr (ComplexLogarithmRemainder.normSq_scale D h) (.eqRefl _) hi.andE₂.andE₂.andE₂
  have grow : Γ ⊢[PRAAx] le (A*B) (A*B*succ i) :=
    le_congr (one_mul (A*B)) (mul_comm (succ i) (A*B))
      (mul_le_mul_right (A*B) (zero_lt_succ i))
  exact le_congr (congrMul (.eqRefl _) (ComplexLogarithmRemainder.normSq_neg h)).eqSymm
    (by ipra_ring) (le_trans old (sq_le_sq grow))

theorem factor_unit_error (h B A D i : PTm n) (hi : Γ ⊢[PRAAx] input h B A D) : Γ ⊢[PRAAx]
    distanceBounded (factor i (ComplexLogarithmRemainder.neg h) B) qone A D :=
  GaussianRationalReciprocal.bound_congr (factor_difference h B i hi.andE₁).eqSymm (.eqRefl _) (.eqRefl _)
    (small_fraction_bound h B A D i hi)

theorem factor_bound (h B A D i : PTm n) (hi : Γ ⊢[PRAAx] input h B A D) : Γ ⊢[PRAAx]
    bounded (factor i (ComplexLogarithmRemainder.neg h) B) two one := by
  have hb := GaussianGammaLocalPoleGuards.local_step_disk h B A D hi.andE₂.andE₁ hi.andE₂.andE₂.andE₁ hi.andE₂.andE₂.andE₂
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianGammaEulerHead.factor_bound i (ComplexLogarithmRemainder.neg h) one B hi.andE₁
      (le_congr (.eqRefl _) (by ipra_ring) (ComplexLogarithmRemainder.bounded_neg hb)))

theorem correction_zero (h B : PTm n) : Γ ⊢[PRAAx] correction h B zero ≐ qone :=
  GaussianRationalFiniteProduct.product_zero _ _
theorem correction_succ (h B j : PTm n) : Γ ⊢[PRAAx]
    correction h B (succ j) ≐ qmul (correction h B j) (factor j (ComplexLogarithmRemainder.neg h) B) := product_step _ _ _

theorem budget_growth (A j : PTm n) : Γ ⊢[PRAAx] le (two*budget A j+A) (budget A (succ j)) := by
  have hp := unit_positive (Γ := Γ) j
  have step := natEq (pw_succ (Γ := Γ) two j)
  ipra_le 𝔞 A*sl hp+𝔞 A*𝔞(unit j) using
    unfold budget unit
    ipra_simps
    rw [step]
    ring

theorem error_zero (h B A D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    distanceBounded (correction h B zero) qone (budget A zero) D :=
  distance_congr (correction_zero h B).eqSymm (.eqRefl _) (by unfold budget; ipra_ring) (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero qone D hD)

theorem error_step (h B A D j : PTm n) (hi : Γ ⊢[PRAAx] input h B A D)
    (ih : Γ ⊢[PRAAx] distanceBounded (correction h B j) qone (budget A j) D) : Γ ⊢[PRAAx]
    distanceBounded (correction h B (succ j)) qone (budget A (succ j)) D := by
  have raw := GaussianNameArithmetic.product_distance (correction h B j) qone (factor j (ComplexLogarithmRemainder.neg h) B) qone
    (budget A j) A D two one hi.andE₂.andE₁ ih (factor_unit_error h B A D j hi)
    (factor_bound h B A D j hi) GaussianRationalReciprocal.qone_bounded
  have aligned : Γ ⊢[PRAAx] distanceBounded (correction h B (succ j)) qone (two*budget A j+A) D :=
    distance_congr (correction_succ h B j).eqSymm
    (GaussianReciprocalHorner.qmul_one_right qone qone_canonical) (by ipra_ring) (.eqRefl _) raw
  exact distance_radius_mono _ _ _ _ _ _ hi.andE₂.andE₁ hi.andE₂.andE₁
    (mul_le_mul_right D (budget_growth A j)) aligned

/-- The inducted formula is one actual finite-product distance. -/
theorem correction_error (h B A D j : PTm n) (hi : Γ ⊢[PRAAx] input h B A D) : Γ ⊢[PRAAx]
    distanceBounded (correction h B j) qone (budget A j) D := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift h) (Syn.shift B) (Syn.shift A) (Syn.shift D) := by
    simpa [Fm.shift,Syn.shift] using hi.shift
  have hall : Γ ⊢[PRAAx] .all (distanceBounded
      (correction (Syn.shift h) (Syn.shift B) (var 0)) qone (budget (Syn.shift A) (var 0)) (Syn.shift D)) := by
    ipra_qfind [GaussianRationalMetric.subst_distanceBounded, subst_correction, subst_budget,
        GaussianRationalSyntheticDivision.subst_qone]
    · exact error_zero h B A D hi.andE₂.andE₁
    · exact error_step _ _ _ _ _ hs.wk Prf.hyp0
  simpa only [GaussianRationalMetric.subst_distanceBounded,subst_correction,subst_budget,
    GaussianRationalSyntheticDivision.subst_qone,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE j
/-- Both original factor constructors normalize the SAME native value. -/
theorem pole_factor_code (h B i : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    GaussianGammaPoleFiniteFactors.factor h B (succ i) ≐ factor i (ComplexLogarithmRemainder.neg h) B := by
  have hE := positive_product _ _ hB (zero_lt_succ i)
  have same : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.neg (GaussianGammaLocalPoleGuards.center h B (succ i)))
      (GaussianGammaEulerHeadLower.translated (ComplexLogarithmRemainder.neg h) B (succ i)) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianGammaLocalPoleGuards.center,GaussianGammaEulerHeadLower.translated,
        GaussianGammaPoleZeros.poleNumerator,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg,
        GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ring
  exact GaussianRationalHorner.canonical_unique _ _ _ (B*succ i)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hE) (GaussianRationalHorner.qadd_canonical _ _) hE
    (GaussianRationalHorner.represents_congr (.eqRefl _) same (.eqRefl _)
      (GaussianRationalHorner.ofGaussian_represents _ _ hE))
    (GaussianGammaEulerHeadLower.factor_represents _ _ _ hB)

def sameProduct (h B j : PTm n) : Fm PTm n := correction h B j ≐ GaussianGammaPoleFiniteFactors.factorProduct h B j
ipra_subst sameProduct

theorem correction_is_original_product (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] sameProduct h B j := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have hall : Γ ⊢[PRAAx] .all (sameProduct (Syn.shift h) (Syn.shift B) (var 0)) := by
    ipra_qfind [subst_sameProduct]
    · exact (correction_zero h B).eqTrans (GaussianRationalFiniteProduct.product_zero _ _).eqSymm
    · exact (correction_succ _ _ _).eqTrans ((qmul_congr Prf.hyp0 (pole_factor_code _ _ _ bs.wk).eqSymm).eqTrans
        (GaussianGammaPoleFiniteFactors.factor_succ _ _ _).eqSymm)
  simpa only [subst_sameProduct,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE j

theorem original_product_error (h B A D j : PTm n) (hi : Γ ⊢[PRAAx] input h B A D) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaPoleFiniteFactors.factorProduct h B j) qone (budget A j) D :=
  distance_congr (correction_is_original_product h B j hi.andE₁) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (correction_error h B A D j hi)

theorem signed_factorial_bound (j : PTm n) : Γ ⊢[PRAAx]
    bounded (GaussianGammaPoleFiniteFactors.signedFactorial j) (Products.fact j) one := by
  have minus := GaussianRationalReciprocal.bounded_negative qone one one (le_refl (Γ := Γ) one) GaussianRationalReciprocal.qone_bounded
  have powBound : Γ ⊢[PRAAx] bounded (GaussianRationalReciprocal.power GaussianRationalMatrixFiniteSums.minusOne j) one one :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (GaussianPolynomialPerturbation.one_power j)
      (GaussianPolynomialPerturbation.one_power j) (GaussianRationalReciprocal.bounded_power _ _ _ _ (le_refl one) minus)
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) powBound
      (GaussianNamedNaturalScale.natural_point_bound (Products.fact j)))

/-- The actual finite quotient after removing h/B tends to (-1)^j*j!.
This supplies the polynomial part of C23; named P(1+h) continuity remains
an explicit later analytic obligation. No division by h is performed. -/
theorem finite_pole_quotient_error (h B A D j : PTm n) (hi : Γ ⊢[PRAAx] input h B A D) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaPoleFiniteFactors.differenceProduct h B j)
      (GaussianGammaPoleFiniteFactors.signedFactorial j) (Products.fact j*budget A j) D := by
  have raw := GaussianApproximateInverseDistance.multiply_distance (GaussianGammaPoleFiniteFactors.signedFactorial j) _ _
    (Products.fact j) (budget A j) D hi.andE₂.andE₁ (signed_factorial_bound j) (original_product_error h B A D j hi)
  exact distance_congr (GaussianGammaPoleFiniteFactors.finite_pole_factors h B j hi.andE₁).eqSymm
    (GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalHorner.qmul_canonical _ _))
    (.eqRefl _) (.eqRefl _) raw

/-- Original correction, finite quotient, signed factorial, budget and denominator. -/
def output (h B A D j : PTm n) : PTm n := pairT (GaussianGammaPoleFiniteFactors.factorProduct h B j)
  (pairT (GaussianGammaPoleFiniteFactors.differenceProduct h B j)
    (pairT (GaussianGammaPoleFiniteFactors.signedFactorial j) (pairT (budget A j) D)))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (h B A D j : PTm n) : PTm n := PTm.app outputF ![h,B,A,D,j]
ipra_subst output
ipra_subst run

theorem program_at (h B A D j : PTm n) : Γ ⊢[PRAAx] run h B A D j ≐ output h B A D j := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![h,B,A,D,j]
theorem returned_correction (h B A D j : PTm n) : Γ ⊢[PRAAx]
    fstT (run h B A D j) ≐ GaussianGammaPoleFiniteFactors.factorProduct h B j :=
  (program_at h B A D j).fstE
theorem returned_quotient (h B A D j : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run h B A D j)) ≐ GaussianGammaPoleFiniteFactors.differenceProduct h B j :=
  (program_at h B A D j).sndE.fstE
theorem returned_signed_factorial (h B A D j : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run h B A D j))) ≐ GaussianGammaPoleFiniteFactors.signedFactorial j :=
  (program_at h B A D j).sndE.sndE.fstE

theorem returned_correction_error (h B A D j : PTm n) (hi : Γ ⊢[PRAAx] input h B A D) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run h B A D j)) qone (budget A j) D :=
  distance_congr (returned_correction h B A D j).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (original_product_error h B A D j hi)
theorem returned_quotient_error (h B A D j : PTm n) (hi : Γ ⊢[PRAAx] input h B A D) : Γ ⊢[PRAAx]
    distanceBounded (fstT (sndT (run h B A D j))) (fstT (sndT (sndT (run h B A D j)))) (Products.fact j*budget A j) D :=
  distance_congr (returned_quotient h B A D j).eqSymm (returned_signed_factorial h B A D j).eqSymm
    (.eqRefl _) (.eqRefl _) (finite_pole_quotient_error h B A D j hi)

theorem actual_original_pole_correction_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ GaussianGammaPoleFiniteFactors.factor (var 0) (var 1) (succ (var 2)) ≐
      factor (var 2) (ComplexLogarithmRemainder.neg (var 0)) (var 1)) := closeUniv 3 (.impI (pole_factor_code _ _ _ Prf.hyp0))
theorem original_finite_pole_correction_continuity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) ⟶ distanceBounded
      (GaussianGammaPoleFiniteFactors.factorProduct (var 0) (var 1) (var 4)) qone (budget (var 2) (var 4)) (var 3)) :=
  closeUniv 5 (.impI (original_product_error _ _ _ _ _ Prf.hyp0))
theorem original_finite_C23_polynomial_quotient_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) ⟶ distanceBounded
      (GaussianGammaPoleFiniteFactors.differenceProduct (var 0) (var 1) (var 4))
      (GaussianGammaPoleFiniteFactors.signedFactorial (var 4)) (Products.fact (var 4)*budget (var 2) (var 4)) (var 3)) :=
  closeUniv 5 (.impI (finite_pole_quotient_error _ _ _ _ _ Prf.hyp0))
theorem actual_pole_correction_continuity_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_pole_quotient_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) ⟶ distanceBounded
      (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))
      (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))))
      (Products.fact (var 4)*budget (var 2) (var 4)) (var 3)) := closeUniv 5 (.impI (returned_quotient_error _ _ _ _ _ Prf.hyp0))


end LeanProofs.IPRA.Analysis.GaussianGammaPoleFactorContinuity
