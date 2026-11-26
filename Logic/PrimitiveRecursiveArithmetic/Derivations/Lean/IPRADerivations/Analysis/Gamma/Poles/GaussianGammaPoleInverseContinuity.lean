import IPRADerivations.Analysis.Gamma.Poles.GaussianGammaPoleFactorContinuity
import IPRADerivations.Analysis.Gamma.Poles.GaussianGammaPoleMultiplier
import IPRADerivations.Analysis.Names.Rates.GaussianRationalLowerPerturbation

/-!
# The original inverse pole factors on the half disk

For an encoded increment of norm at most `A/D ≤ 1/2`, the actual
inverse correction product differs from one by at most
`A*j*2^j*2^j/D`. The same bound applies after multiplication by the
signed inverse factorial. Both estimates include the center.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPoleInverseContinuity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaPoleFactorContinuity (input pole_factor_code factor_unit_error original_product_error)
open GaussianGammaPoleFiniteFactors (factor factorProduct)
open GaussianGammaPoleMultiplier
  (inverseFactorBody inverseFactorProduct inverseFactorProduct_succ signedInverseFactorial)
open GaussianRationalHorner (ofGaussian qmul qmul_canonical positive_product)
open GaussianRationalSyntheticDivision (qone qone_canonical)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (reciprocal qone_bounded bound_congr bounded_product)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianReciprocalHorner (qmul_one_right)
open ComplexLogarithmRemainder (oneCode normSq scale normSq_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ subst_zero subst_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def halfDisk (h B : PTm n) : Fm PTm n :=
  ComplexLogarithmRemainder.bounded (scale two h) B

@[simp] theorem subst_halfDisk {l : ℕ} (σ : Fin n → PTm l) (h B : PTm n) :
    (halfDisk h B).subst σ = halfDisk (Syn.subst σ h) (Syn.subst σ B) := by
  simp [halfDisk, ComplexLogarithmRemainder.bounded]

private theorem two_positive : Γ ⊢[PRAAx] le one (two : PTm n) := zero_lt_succ one

private theorem half_disk (h B A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hAD : Γ ⊢[PRAAx] le (two*A) D)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (scale D h) (A*B)) :
    Γ ⊢[PRAAx] halfDisk h B := by
  have old := le_congr (normSq_scale D h) (.eqRefl _) hh
  have grows : Γ ⊢[PRAAx] le ((two*A)*B) (D*B) := mul_le_mul_right B hAD
  have scaled : Γ ⊢[PRAAx] le ((D*D)*(two*two*normSq h)) (((two*A)*B)*((two*A)*B)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (two*two) old)
  have step : Γ ⊢[PRAAx] le ((D*D)*(two*two*normSq h)) ((D*D)*(B*B)) :=
    le_trans scaled (le_congr (.eqRefl _) (by ipra_ring) (sq_le_sq grows))
  exact le_congr (normSq_scale two h).eqSymm (.eqRefl _)
    (RationalValueBounds.positive_cancel (positive_product D D hD hD) step)

private theorem inverse_factor_bound (h B i : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] halfDisk h B) :
    Γ ⊢[PRAAx] bounded (reciprocal (factor h B (succ i))) two one := by
  have small : Γ ⊢[PRAAx] input h B one two :=
    .andI hB (.andI two_positive (.andI two_positive (le_congr (.eqRefl _) (by ipra_ring) hh)))
  have close := distance_congr (pole_factor_code h B i hB).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (factor_unit_error h B one two i small)
  have low := GaussianRationalLowerPerturbation.lower_near_unit _ one two two_positive two_positive close
  exact GaussianRationalLowerBounds.inverse_bound _ one two (le_refl one) two_positive
    (GaussianRationalLowerBounds.lower_congr (.eqRefl _) ((succ_monus_succ one zero).eqTrans (monus_zero one))
      (.eqRefl _) low)

theorem inverse_product_bound (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] halfDisk h B) :
    Γ ⊢[PRAAx] bounded (inverseFactorProduct h B j) (unit j) one := by
  have b : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa [Fm.shift, Syn.shift] using hB.shift
  have r : Γ.map Fm.shift ⊢[PRAAx] halfDisk (Syn.shift h) (Syn.shift B) := by
    simpa [Fm.shift, Syn.shift] using hh.shift
  have all : Γ ⊢[PRAAx] .all (bounded (inverseFactorProduct (Syn.shift h) (Syn.shift B) (var 0))
      (unit (var 0)) one) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [GaussianRationalMetric.subst_bounded, GaussianGammaPoleMultiplier.subst_inverseFactorProduct,
        GaussianCoefficientNameBounds.subst_unit, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        one, subst_succ, subst_zero]
      exact bound_congr (GaussianRationalFiniteProduct.product_zero inverseFactorBody _).eqSymm
        (pw_zero two).eqSymm (.eqRefl _) qone_bounded
    · simp only [GaussianRationalMetric.subst_bounded, GaussianGammaPoleMultiplier.subst_inverseFactorProduct,
        GaussianCoefficientNameBounds.subst_unit, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        one, subst_succ, subst_zero]
      exact bound_congr (inverseFactorProduct_succ _ _ _).eqSymm (pw_succ two _).eqSymm (one_mul one)
        (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) Prf.hyp0
          (inverse_factor_bound _ _ _ b.wk r.wk))
  simpa only [GaussianRationalMetric.subst_bounded, GaussianGammaPoleMultiplier.subst_inverseFactorProduct,
    GaussianCoefficientNameBounds.subst_unit, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    one, subst_succ, subst_zero] using
    all.allE j

def budget (A j : PTm n) : PTm n := unit j*GaussianGammaPoleFactorContinuity.budget A j

theorem original_inverse_product_error (h B A D j : PTm n)
    (hi : Γ ⊢[PRAAx] input h B A D) (hrad : Γ ⊢[PRAAx] le (two*A) D) :
    Γ ⊢[PRAAx] distanceBounded (inverseFactorProduct h B j) qone (budget A j) D := by
  let f := factorProduct h B j
  let g := inverseFactorProduct h B j
  have hB := hi.andE₁
  have hD := hi.andE₂.andE₁
  have hh := half_disk h B A D hD hrad hi.andE₂.andE₂.andE₂
  have inverse : Γ ⊢[PRAAx] qmul g f ≐ qone :=
    (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (GaussianGammaPoleMultiplier.product_inverse h B one one two j hB (le_refl one) two_positive
        (le_congr (by ipra_ring) (.eqRefl _) (le_refl two))
        (le_congr (.eqRefl _) (by ipra_ring) hh))
  have canon : Γ ⊢[PRAAx] GaussianRationalHorner.canonical g :=
    GaussianRationalFiniteProduct.product_canonical inverseFactorBody j (pairT h B)
  exact distance_congr (qmul_one_right g canon) inverse (.eqRefl _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance g qone f (unit j) _ D hD
      (inverse_product_bound h B j hB hh)
      (distance_symmetric _ _ _ _ hD (original_product_error h B A D j hi)))

theorem signed_inverse_factorial_bound (j : PTm n) :
    Γ ⊢[PRAAx] bounded (signedInverseFactorial j) one one := by
  let d := Products.fact j
  have hd := GaussianRationalPolynomialExponential.factorial_positive (Γ := Γ) j
  have root : Γ ⊢[PRAAx] bounded (ofGaussian oneCode d) one one := by
    apply (GaussianRationalMetric.bounded_iff _ _ _ _ _ hd (le_refl one)
      (GaussianRationalHorner.ofGaussian_represents _ _ hd)).iffMpr
    apply le_congr ?_ (by ipra_ring) (sq_le_sq hd)
    have norm := natEq (ComplexLogarithmRemainder.normSq_one (Γ := Γ))
    apply deriveNat
    ipra_simps
    rw [norm]
    ring
  have minus := GaussianRationalReciprocal.bounded_negative qone one one (le_refl (Γ := Γ) one) qone_bounded
  have sign := bound_congr (.eqRefl _) (GaussianPolynomialPerturbation.one_power j)
    (GaussianPolynomialPerturbation.one_power j)
    (GaussianRationalReciprocal.bounded_power _ _ _ _ (le_refl one) minus)
  exact bound_congr (.eqRefl _) (one_mul one) (one_mul one)
    (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) sign root)

theorem original_regular_multiplier_error (h B A D j : PTm n)
    (hi : Γ ⊢[PRAAx] input h B A D) (hrad : Γ ⊢[PRAAx] le (two*A) D) :
    Γ ⊢[PRAAx] distanceBounded (qmul (signedInverseFactorial j) (inverseFactorProduct h B j))
      (signedInverseFactorial j) (budget A j) D := by
  exact distance_congr (.eqRefl _) (qmul_one_right _ (qmul_canonical _ _)) (one_mul _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance _ _ qone one _ D hi.andE₂.andE₁
      (signed_inverse_factorial_bound j) (original_inverse_product_error h B A D j hi hrad))

theorem original_inverse_pole_factor_continuity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) ⟶ le (two*var 2) (var 3) ⟶
      distanceBounded (inverseFactorProduct (var 0) (var 1) (var 4)) qone (budget (var 2) (var 4)) (var 3)) :=
  closeUniv 5 (.impI (.impI (original_inverse_product_error _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_regular_pole_multiplier_continuity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) ⟶ le (two*var 2) (var 3) ⟶
      distanceBounded (qmul (signedInverseFactorial (var 4)) (inverseFactorProduct (var 0) (var 1) (var 4)))
        (signedInverseFactorial (var 4)) (budget (var 2) (var 4)) (var 3)) :=
  closeUniv 5 (.impI (.impI (original_regular_multiplier_error _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaPoleInverseContinuity
