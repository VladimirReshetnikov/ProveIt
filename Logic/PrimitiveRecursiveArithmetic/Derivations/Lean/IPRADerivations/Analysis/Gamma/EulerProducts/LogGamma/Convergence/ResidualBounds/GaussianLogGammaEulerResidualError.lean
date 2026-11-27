import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.ResidualBounds.GaussianLogGammaEulerResidualDomain
import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmLinearRemainder

/-!
# The normalized quadratic error of an Euler logarithm row

The original finite and named local logarithm both use the native
centered offset of the normalized row. Its linear term is the exact
Euler rational z/k. The original base denominator cancels from both
error budgets, leaving R²/k² and the existing observation error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerResidualError

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerResidualDomain (source rowOffset linearTerm admission linear_point)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def localPoint (p A B D neg R k : PTm n) : PTm n :=
  GaussianLocalLogarithmName.point p (rowOffset A B D neg k) (R*D) (D*k)

theorem finite_linear_error (L A B D neg R k : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hk : Γ ⊢[PRAAx] le one k) (hlarge : Γ ⊢[PRAAx] le (num 8*R) k) :
    Γ ⊢[PRAAx] distanceBounded (GaussianFiniteLogarithmSampler.sample (rowOffset A B D neg k) (D*k) L)
      (linearTerm A B D neg k) (R*R) (k*k) := by
  let w := rowOffset A B D neg k
  let d := D*k
  have hd := positive_product D k h.andE₁.andE₂ hk
  have hs := GaussianRightHalfPlaneLogarithmOffset.local_source (A+k*D) B d neg (R*D)
    (admission A B D neg R k h hk hlarge)
  have old := GaussianLocalLogarithmLinearRemainder.finite_linear_remainder w (R*D) d L hs
  have new := distance_radius_mono _ _ _ _ (R*R) (k*k) (positive_product _ _ hd hd) (positive_product _ _ hk hk)
    (le_of_eq_add (d := zero) (by ipra_ring)) old
  exact distance_congr (.eqRefl _) (linear_point A B D neg k h.andE₁.andE₂ hk) (.eqRefl _) (.eqRefl _) new

theorem local_sample_error (p A B D neg R k : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hk : Γ ⊢[PRAAx] le one k) (hlarge : Γ ⊢[PRAAx] le (num 8*R) k) :
    Γ ⊢[PRAAx] distanceBounded (localPoint p A B D neg R k)
      (linearTerm A B D neg k) (R*R*unit p+k*k) (k*k*unit p) := by
  let w := rowOffset A B D neg k
  let d := D*k
  have hd := positive_product D k h.andE₁.andE₂ hk
  have hs := GaussianRightHalfPlaneLogarithmOffset.local_source (A+k*D) B d neg (R*D)
    (admission A B D neg R k h hk hlarge)
  have old := GaussianLocalLogarithmLinearRemainder.original_linear_remainder p w (R*D) d hs
  have b := positive_product _ _ (positive_product _ _ hd hd) (unit_positive p)
  have e := positive_product _ _ (positive_product _ _ hk hk) (unit_positive p)
  have new := distance_radius_mono _ _ _ _ (R*R*unit p+k*k) (k*k*unit p) b e
    (le_of_eq_add (d := zero) (by dsimp only [d]; ipra_ring)) old
  exact distance_congr (.eqRefl _) (linear_point A B D neg k h.andE₁.andE₂ hk) (.eqRefl _) (.eqRefl _) new

theorem actual_normalized_Euler_row_finite_quadratic_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      ((source (var 0) (var 1) (var 2) (var 3) (var 4) ⋏ (le one (var 5) ⋏ le (num 8*var 4) (var 5))) ⟶
        distanceBounded (GaussianFiniteLogarithmSampler.sample (rowOffset (var 0) (var 1) (var 2) (var 3) (var 5))
          (var 2*var 5) (var 6)) (linearTerm (var 0) (var 1) (var 2) (var 3) (var 5))
          (var 4*var 4) (var 5*var 5)) :=
  closeUniv 7 (.impI (finite_linear_error _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_normalized_Euler_row_sample_quadratic_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      ((source (var 0) (var 1) (var 2) (var 3) (var 4) ⋏ (le one (var 5) ⋏ le (num 8*var 4) (var 5))) ⟶
        distanceBounded (localPoint (var 6) (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
          (linearTerm (var 0) (var 1) (var 2) (var 3) (var 5))
          (var 4*var 4*unit (var 6)+var 5*var 5) (var 5*var 5*unit (var 6))) :=
  closeUniv 7 (.impI (local_sample_error _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerResidualError
