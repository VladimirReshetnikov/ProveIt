import IPRADerivations.Analysis.GaussianEulerLogarithmicMultiplier
import IPRADerivations.Analysis.GaussianExponentialLinearRemainder

/-!
# Actual logarithmic Euler factors under a finite parameter increment

At a fixed original time and query, multiplication by the actual
increment h*log(t) raises the unrestricted numerical logarithmic order
from j to j+1. The actual factorial-sum exponential of that increment
has a uniform quadratic remainder, supplied by its proved finite tail.
This is a finite, evaluated parameter model. No Taylor error or equality
with an independently retimed perturbed Euler observation is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicParameterIncrement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicMultiplier (sample majorant logRadius)
open GaussianPositiveRationalLogarithm (sample)
open GaussianRationalHorner (qadd qmul ofGaussian canonical positive_product)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr)
open GaussianRationalReciprocal (power bound_congr bounded_product)
open GaussianRationalMetric (distanceBounded bounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def increment (s h D a b : PTm n) : PTm n := qmul (ofGaussian h D) (GaussianPositiveRationalLogarithm.sample s a b)
def linearModel (s j z B h D a b : PTm n) : PTm n :=
  qadd (GaussianEulerLogarithmicMultiplier.sample s j z B a b)
    (qmul (ofGaussian h D) (GaussianEulerLogarithmicMultiplier.sample s (succ j) z B a b))
def finiteModel (s K j z B h D a b : PTm n) : PTm n :=
  qmul (GaussianEulerLogarithmicMultiplier.sample s j z B a b)
    (GaussianRationalPolynomialExponential.scalarSum (increment s h D a b) K)
def curvature (j R E T : PTm n) : PTm n := majorant j R E T*logRadius E T*logRadius E T

def source (z R B E T a b h D X Y : PTm n) : Fm PTm n :=
  GaussianEulerLogarithmicMultiplier.source z R B E T a b ⋏
    (le one D ⋏ (le one Y ⋏ (le (logRadius E T*X) Y ⋏ bounded (ofGaussian h D) X Y)))

@[simp] theorem subst_increment {m : ℕ} (σ : Fin n → PTm m) (s h D a b : PTm n) :
    Syn.subst σ (increment s h D a b) = increment (Syn.subst σ s) (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ a) (Syn.subst σ b) := by simp [increment]
@[simp] theorem subst_linearModel {m : ℕ} (σ : Fin n → PTm m) (s j z B h D a b : PTm n) :
    Syn.subst σ (linearModel s j z B h D a b) = linearModel (Syn.subst σ s) (Syn.subst σ j) (Syn.subst σ z)
      (Syn.subst σ B) (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ a) (Syn.subst σ b) := by simp [linearModel]
@[simp] theorem subst_finiteModel {m : ℕ} (σ : Fin n → PTm m) (s K j z B h D a b : PTm n) :
    Syn.subst σ (finiteModel s K j z B h D a b) = finiteModel (Syn.subst σ s) (Syn.subst σ K) (Syn.subst σ j)
      (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ a) (Syn.subst σ b) := by simp [finiteModel]
@[simp] theorem subst_curvature {m : ℕ} (σ : Fin n → PTm m) (j R E T : PTm n) :
    Syn.subst σ (curvature j R E T) = curvature (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by simp [curvature]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B E T a b h D X Y : PTm n) :
    (source z R B E T a b h D X Y).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ h)
      (Syn.subst σ D) (Syn.subst σ X) (Syn.subst σ Y) := by simp [source]

/-- The order successor is the actual numerical power successor. -/
theorem original_order_increment (s j z B h D a b : PTm n) : Γ ⊢[PRAAx]
    qmul (GaussianEulerLogarithmicMultiplier.sample s j z B a b) (increment s h D a b) ≐
      qmul (ofGaussian h D) (GaussianEulerLogarithmicMultiplier.sample s (succ j) z B a b) := by
  let e := GaussianEulerIntegrandName.sample s z B a b
  let l := GaussianPositiveRationalLogarithm.sample s a b
  let c := ofGaussian h D
  exact (GaussianRationalPowerAlgebra.qmul_shuffle e (power l j) c l).eqTrans
    ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative e c)
      (GaussianRationalReciprocal.power_succ l j).eqSymm).eqTrans
        (GaussianReciprocalHorner.qmul_associative c e (power l (succ j))))

theorem original_linear_model (s j z B h D a b : PTm n) : Γ ⊢[PRAAx]
    qmul (GaussianEulerLogarithmicMultiplier.sample s j z B a b) (qadd qone (increment s h D a b)) ≐
      linearModel s j z B h D a b :=
  (GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
    (qadd_congr (GaussianReciprocalHorner.qmul_one_right _
      (GaussianEulerLogarithmicMultiplier.original_sample_canonical s j z B a b))
      (original_order_increment s j z B h D a b))

theorem original_increment_bound (s z R B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B E T a b h D X Y) : Γ ⊢[PRAAx]
    bounded (increment s h D a b) (logRadius E T*X) Y :=
  bound_congr (.eqRefl _) (mul_comm _ _) (by ipra_ring)
    (bounded_product _ _ _ _ _ _ hs.andE₂.andE₂.andE₁ (le_refl one) hs.andE₂.andE₂.andE₂.andE₂
      (GaussianCompactLogarithmBounds.sample_bound s a b E T hs.andE₁.andE₁.andE₂.andE₁ hs.andE₁.andE₂))

/-- The evaluated finite exponential uses its actual factorial sum and
any original cutoff K>=1. No exponential approximation is a premise. -/
theorem original_finite_remainder (s K j z R B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B E T a b h D X Y) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    distanceBounded (finiteModel s K j z B h D a b) (linearModel s j z B h D a b)
      (curvature j R E T*X*X) (Y*Y) := by
  have yy := positive_product _ _ hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₁
  have rem := GaussianExponentialLinearRemainder.original_finite_linear_remainder (increment s h D a b)
    (logRadius E T*X) Y K hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₁
    (original_increment_bound s z R B E T a b h D X Y hs) (GaussianRationalHorner.qmul_canonical _ _) hK
  have scaled := bounded_product _ _ _ _ _ _ (le_refl one) yy
    (GaussianEulerLogarithmicMultiplier.original_sample_bound s j z R B E T a b hs.andE₁) rem
  exact bound_congr
    ((GaussianRationalRoundedPower.multiplication_difference _ _ _).eqSymm.eqTrans
      (GaussianRationalSyntheticDivision.qsub_congr (.eqRefl _) (original_linear_model s j z B h D a b)))
    (by unfold curvature; ipra_ring) (by ipra_ring) scaled

/-- Radius one is the genuine input radius of this actual constant
exponential; its internal input query and cutoff are unchanged. -/
theorem original_constant_exponential_remainder (p s j z R B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B E T a b h D X Y) : Γ ⊢[PRAAx]
    distanceBounded
      (qmul (GaussianEulerLogarithmicMultiplier.sample s j z B a b)
        (GaussianRadiusExponentialName.sample GaussianGammaCanonicalExponent.constantF one p (increment s h D a b)))
      (linearModel s j z B h D a b) (curvature j R E T*X*X) (Y*Y) := by
  have yy := positive_product _ _ hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₁
  have rem := GaussianExponentialLinearRemainder.original_constant_exponential_linear_remainder
    (increment s h D a b) (logRadius E T*X) Y p hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₁
    (original_increment_bound s z R B E T a b h D X Y hs) (GaussianRationalHorner.qmul_canonical _ _)
  have scaled := bounded_product _ _ _ _ _ _ (le_refl one) yy
    (GaussianEulerLogarithmicMultiplier.original_sample_bound s j z R B E T a b hs.andE₁) rem
  exact bound_congr
    ((GaussianRationalRoundedPower.multiplication_difference _ _ _).eqSymm.eqTrans
      (GaussianRationalSyntheticDivision.qsub_congr (.eqRefl _) (original_linear_model s j z B h D a b)))
    (by unfold curvature; ipra_ring) (by ipra_ring) scaled

theorem original_runtime_order_increment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (qmul (GaussianEulerLogarithmicMultiplier.sample (var 0) (var 1) (var 2) (var 3) (var 6) (var 7))
      (increment (var 0) (var 4) (var 5) (var 6) (var 7)) ≐
      qmul (ofGaussian (var 4) (var 5))
        (GaussianEulerLogarithmicMultiplier.sample (var 0) (succ (var 1)) (var 2) (var 3) (var 6) (var 7))) :=
  closeUniv 8 (original_order_increment _ _ _ _ _ _ _ _)

theorem original_finite_parameter_increment_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
    ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) ⋏ le one (var 1)) ⟶
      distanceBounded (finiteModel (var 0) (var 1) (var 2) (var 3) (var 5) (var 10) (var 11) (var 8) (var 9))
        (linearModel (var 0) (var 2) (var 3) (var 5) (var 10) (var 11) (var 8) (var 9))
        (curvature (var 2) (var 4) (var 6) (var 7)*var 12*var 12) (var 13*var 13)) :=
  closeUniv 14 (.impI (original_finite_remainder _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicParameterIncrement
