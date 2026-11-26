import IPRADerivations.Analysis.Trigonometry.SineProducts.GaussianSineProductScaledArgumentIdentity

/-!
# Relative scale of the two actual sine-product arguments

The exact rational factor z/(Bk) relates πz/(Bm) to kπ/m at a common
quarter-turn observation. A cofinal comparison restores the two
programs' actual, independently selected observation clocks.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductRelativeArgument

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianSineProductScaledArguments (coefficient nameF data)
open GaussianSineProductScaledArgumentIdentity (realRootData)
open ComplexLogarithmRemainder (scale mul oneCode)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianArctangentQuarterExponential (quarterF quarter_regular)
open GaussianBoundedConstantProductName (clock)
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical qmul qmul_canonical
  qmul_represents represents_rescale represents_congr canonical_unique positive_product)
open GaussianRationalMetric (bounded bounded_iff distanceBounded)
open GaussianRootAlgebra (re_mul im_mul re_scale im_scale re_one im_one equal_of_values)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianNamedSincSamples (common_late_distance)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def relative (z B k : PTm n) : PTm n := ofGaussian z (B*k)

@[simp] theorem subst_relative {l : ℕ} (σ : Fin n → PTm l) (z B k : PTm n) :
    Syn.subst σ (relative z B k) = relative (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ k) := by
  simp [relative]

theorem relative_bound (z R B k : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (relative z B k) R k := by
  have hD := positive_product B k hB hk
  exact (bounded_iff _ z (B*k) R k hD hk (ofGaussian_represents _ _ hD)).iffMpr
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (k*k) hz))

theorem relative_coefficient (z B m k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hm : Γ ⊢[PRAAx] le one m) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] qmul (relative z B k) (coefficient (scale k oneCode) one m) ≐ coefficient z B m := by
  let i : PTm n := ComplexLogarithmRemainder.neg imaginaryCode
  let a := scale two (mul i (scale k oneCode))
  let b := scale two (mul i z)
  have hR := positive_product B k hB hk
  have hS := positive_product one m (le_refl one) hm
  have hB' := positive_product B m hB hm
  have lhs := qmul_represents (relative z B k) (coefficient (scale k oneCode) one m) z a
    (B*k) (one*m) hR hS (ofGaussian_represents _ _ hR) (ofGaussian_represents _ _ hS)
  have rhs := represents_rescale (coefficient z B m) b (B*m) k (ofGaussian_represents _ _ hB')
  have value : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (mul z a) (scale k b) := by
    dsimp only [a,b]
    apply equal_of_values <;> simp only [re_mul,im_mul,re_scale,im_scale,re_one,im_one] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ _ (qmul_canonical _ _) (ofGaussian_canonical _ _ hB')
    (positive_product _ _ hB' hk) (represents_congr (.eqRefl _) value (by ipra_ring) lhs) rhs

theorem relative_root_sample_at (z B m k x p : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hm : Γ ⊢[PRAAx] le one m) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] qmul (relative z B k) (ap2 nameF p (realRootData k m x)) ≐
      qmul (coefficient z B m) (ap2 quarterF (clock p (two*k)) x) := by
  exact (qmul_congr (.eqRefl _) (GaussianSineProductScaledArguments.sample_at (scale k oneCode) k one m x p)).eqTrans
    ((qmul_associative _ _ _).eqSymm.eqTrans (qmul_congr (relative_coefficient z B m k hB hm hk) (.eqRefl _)))

theorem relative_sample_error (z R B m k x p : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hm : Γ ⊢[PRAAx] le one m) (hk : Γ ⊢[PRAAx] le one k)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B m x))
      (qmul (relative z B k) (ap2 nameF p (realRootData k m x))) ((two*R)*two) (unit p) := by
  let a := clock p (two*R)
  let b := clock p (two*k)
  have gap := common_late_distance (Γ := Γ) quarterF x p a b (quarter_regular x)
    (le_add_right _ _) (le_add_right _ _)
  have c := GaussianSineProductScaledArguments.coefficient_bound z R B m hB hm hz
  have c' := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ (two*R) one hm (le_refl one)
    (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (two*R)) hm) c
  exact distance_congr (GaussianSineProductScaledArguments.sample_at z R B m x p).eqSymm
    (relative_root_sample_at z B m k x p hB hm hk).eqSymm (.eqRefl _) (.eqRefl _)
    (multiply_distance _ _ _ _ _ _ (unit_positive p) c' gap)

end LeanProofs.IPRA.Analysis.GaussianSineProductRelativeArgument
