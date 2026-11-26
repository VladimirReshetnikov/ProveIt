import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerPositiveTimePowerProduct

/-!
# The original complex power at a squared positive rational time

Doubling the exponent coefficient transports the actual power at a
squared time to a power at the original time. The two evaluations keep
their original data and precision schedules.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSquarePower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add scale oneCode)
open GaussianRootAlgebra (sub)
open GaussianEulerIntegrandName (source logarithmF coefficient powerExponentF powerExponentData
  powerRadius powerF powerData power_input)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData multiplyData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_refl cross_at)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (qadd canonical_unique qadd_canonical qadd_represents represents_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- At denominator B, this numerator encodes 2z/B - 1. Its Euler
power therefore has exponent 2(z/B - 1). -/
def doubledMinusOne (z B : PTm n) : PTm n := sub (add z z) (scale B oneCode)

@[simp] theorem subst_doubledMinusOne {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (doubledMinusOne z B) = doubledMinusOne (Syn.subst σ z) (Syn.subst σ B) := by
  simp [doubledMinusOne]

theorem doubled_coefficient (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    coefficient (doubledMinusOne z B) B ≐ qadd (coefficient z B) (coefficient z B) := by
  let w := scale B oneCode
  let v := sub z w
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (sub (doubledMinusOne z B) w) (add v v) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [doubledMinusOne, v, w, GaussianRootAlgebra.re_sub, GaussianRootAlgebra.im_sub,
        GaussianRootAlgebra.re_add, GaussianRootAlgebra.im_add] <;> ring
  have hz := GaussianEulerIntegrandName.coefficient_represents z B hB
  exact canonical_unique _ _ (add v v) B (GaussianRationalMetric.qsub_canonical _ _) (qadd_canonical _ _) hB
    (represents_congr (.eqRefl _) native (.eqRefl _) (GaussianEulerIntegrandName.coefficient_represents _ B hB))
    (qadd_represents _ _ v v B hB hz hz)

theorem exponent_double (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    crossEquivalent (addF powerExponentF powerExponentF) powerExponentF
      (addData (powerExponentData z B a b) (powerExponentData z B a b))
      (powerExponentData (doubledMinusOne z B) B a b) := by
  let x := coefficient z B
  let y := coefficient (doubledMinusOne z B) B
  let ell := GaussianPositiveRationalLogarithm.data a b
  have hx := constant_regular (Γ := Γ) x
  have hy := constant_regular (Γ := Γ) y
  have hl := GaussianPositiveRationalLogarithm.name_regular a b h.andE₂
  have coeff := cross_trans _ _ _ _ _ _ (GaussianGammaEulerShift.constant_sum_cross x x)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (doubled_coefficient z B h.andE₁).eqSymm)
  have distribute := GaussianNameRingLaws.right_distributive constantF constantF logarithmF x x ell hx hx hl
  have replace := GaussianGammaAdjacentCutoff.multiply_cross (addF constantF constantF) constantF logarithmF logarithmF
    (addData x x) y ell ell (add_fast _ _ _ _ hx hx) hy hl hl coeff (cross_refl _ _ hl)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ distribute) replace

theorem original_power_at_square (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    crossEquivalent powerF powerF (powerData z B (a*a) (b*b)) (powerData (doubledMinusOne z B) B a b) := by
  have shifted : Γ ⊢[PRAAx] source (doubledMinusOne z B) B a b := h
  have timeProduct : Γ ⊢[PRAAx] GaussianEulerPositiveTimePowerProduct.source B a b a b :=
    .andI h.andE₁ (.andI h.andE₂ h.andE₂)
  have original := GaussianEulerPositiveTimePowerProduct.original_power_product z B a b a b timeProduct
  have reformulated := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent
    powerExponentF powerExponentF powerExponentF (powerRadius z B a b) (powerRadius z B a b)
    (powerRadius (doubledMinusOne z B) B a b) (powerExponentData z B a b) (powerExponentData z B a b)
    (powerExponentData (doubledMinusOne z B) B a b) (power_input z B a b h) (power_input z B a b h)
    (power_input (doubledMinusOne z B) B a b shifted) (exponent_double z B a b h)
  exact cross_trans _ _ _ _ _ _ original reformulated

theorem actual_original_power_at_square_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent powerF powerF
      (powerData (var 0) (var 1) (var 2*var 2) (var 3*var 3))
      (powerData (doubledMinusOne (var 0) (var 1)) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_power_at_square _ _ _ _ Prf.hyp0))

theorem actual_original_power_at_square_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) (var 5) ⟶
      distanceBounded (ap2 powerF (var 0) (powerData (var 2) (var 3) (var 4*var 4) (var 5*var 5)))
        (ap2 powerF (var 1) (powerData (doubledMinusOne (var 2) (var 3)) (var 3) (var 4) (var 5)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (cross_at _ _ _ _ _ _ (original_power_at_square _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerSquarePower
