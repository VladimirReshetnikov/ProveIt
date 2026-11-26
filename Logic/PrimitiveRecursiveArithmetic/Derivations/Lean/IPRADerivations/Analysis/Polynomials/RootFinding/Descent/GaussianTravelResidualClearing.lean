import IPRADerivations.Analysis.Polynomials.Translation.GaussianTranslationCoefficientBound
import IPRADerivations.Analysis.Inequalities.RationalNonnegativePowerOrder

/-!
# Clearing actual residual budgets in the travel estimate

The actual Gaussian-rational residual bound B0*Q^j gives its exact native
squared comparison, including zero residuals and zero Q. Combining it
with the genuine coefficient/radius inequality cancels only the positive
decoded residual denominator. No coefficient norm or numerator is divided
out. All powers, radii, budgets and counters are numerical inputs.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianTravelResidualClearing

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawDen rawGaussian raw_represents raw_den_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (normNumerator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

alias power_square := Common.pw_double

/-- The point is the actual residual, not a supplied residual value or
representation. Its independently decoded denominator is always positive. -/
theorem norm_budget (z E F q s j : PTm n) (hF : Γ ⊢[PRAAx] le one F)
    (hs : Γ ⊢[PRAAx] le one s)
    (h : Γ ⊢[PRAAx] bounded z (E*pw q j) (F*pw s j)) : Γ ⊢[PRAAx]
    le (normNumerator z*(F*F*pw s (two*j)))
      ((E*E*pw q (two*j))*(rawDen z*rawDen z)) := by
  have hDen := positive_product F (pw s j) hF (RationalNonnegativePowers.denominator_positive s j hs)
  have raw := GaussianRationalMetric.bounded_to_cleared z (rawGaussian z) (rawDen z)
    (E*pw q j) (F*pw s j) (raw_den_positive z) hDen (raw_represents z) h
  have eqLeft : Γ ⊢[PRAAx]
      ((F*pw s j)*(F*pw s j))*normNumerator z ≐ normNumerator z*(F*F*pw s (two*j)) := by
    have e := natEq (power_square (Γ := Γ) s j)
    apply deriveNat
    ipra_simps
    rw [e]
    ring
  have eqRight : Γ ⊢[PRAAx]
      ((E*pw q j)*(E*pw q j))*(rawDen z*rawDen z) ≐ (E*E*pw q (two*j))*(rawDen z*rawDen z) := by
    have e := natEq (power_square (Γ := Γ) q j)
    apply deriveNat
    ipra_simps
    rw [e]
    ring
  exact le_congr eqLeft eqRight raw

/-- A local algebra rule. Both incoming inequalities are proved by the
actual coefficient/radius and residual producers in the source instance. -/
theorem combine_squared_budgets (a b U V L M W nr dr E F q s i j : PTm n)
    (hd : Γ ⊢[PRAAx] le one dr)
    (hCoefficient : Γ ⊢[PRAAx]
      le (L*L*pw (a*V) (two*i)*(dr*dr)) (W*W*M*M*nr*pw (b*U) (two*i)))
    (hResidual : Γ ⊢[PRAAx]
      le (nr*(F*F*pw s (two*j))) ((E*E*pw q (two*j))*(dr*dr))) : Γ ⊢[PRAAx]
    le ((F*L)*(F*L)*pw (a*V) (two*i)*pw s (two*j))
      ((E*W*M)*(E*W*M)*pw q (two*j)*pw (b*U) (two*i)) := by
  have first := mul_le_mul_right (F*F*pw s (two*j)) hCoefficient
  have second := mul_le_mul_right (W*W*M*M*pw (b*U) (two*i)) hResidual
  have start : Γ ⊢[PRAAx]
      le ((dr*dr)*((F*L)*(F*L)*pw (a*V) (two*i)*pw s (two*j)))
        (W*W*M*M*nr*pw (b*U) (two*i)*(F*F*pw s (two*j))) :=
    le_congr (by ipra_ring) (.eqRefl _) first
  have finish : Γ ⊢[PRAAx]
      le (W*W*M*M*nr*pw (b*U) (two*i)*(F*F*pw s (two*j)))
        ((dr*dr)*((E*W*M)*(E*W*M)*pw q (two*j)*pw (b*U) (two*i))) :=
    le_congr (by ipra_ring) (by ipra_ring) second
  exact RationalValueBounds.positive_cancel (positive_product dr dr hd hd) (le_trans start finish)

theorem combined_point_budget (z a b U V L M W E F q s i j : PTm n)
    (hF : Γ ⊢[PRAAx] le one F) (hs : Γ ⊢[PRAAx] le one s)
    (hCoefficient : Γ ⊢[PRAAx]
      le (L*L*pw (a*V) (two*i)*(rawDen z*rawDen z))
        (W*W*M*M*normNumerator z*pw (b*U) (two*i)))
    (hResidual : Γ ⊢[PRAAx] bounded z (E*pw q j) (F*pw s j)) : Γ ⊢[PRAAx]
    le ((F*L)*(F*L)*pw (a*V) (two*i)*pw s (two*j))
      ((E*W*M)*(E*W*M)*pw q (two*j)*pw (b*U) (two*i)) :=
  combine_squared_budgets a b U V L M W _ _ E F q s i j (raw_den_positive z) hCoefficient (norm_budget z E F q s j hF hs hResidual)

theorem actual_residual_power_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 2) ⟶ le one (var 4) ⟶ bounded (var 0) ((var 1)*pw (var 3) (var 5)) ((var 2)*pw (var 4) (var 5)) ⟶
      le (normNumerator (var 0)*((var 2)*(var 2)*pw (var 4) (two*(var 5))))
        (((var 1)*(var 1)*pw (var 3) (two*(var 5)))*(rawDen (var 0)*rawDen (var 0)))) :=
  closeUniv 6 (.impI (.impI (.impI (norm_budget _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem actual_combined_point_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
    (le one (var 9) ⟶ le one (var 11) ⟶
      le ((var 5)*(var 5)*pw ((var 1)*(var 4)) (two*(var 12))*(rawDen (var 0)*rawDen (var 0)))
        ((var 7)*(var 7)*(var 6)*(var 6)*normNumerator (var 0)*pw ((var 2)*(var 3)) (two*(var 12))) ⟶
      bounded (var 0) ((var 8)*pw (var 10) (var 13)) ((var 9)*pw (var 11) (var 13)) ⟶
      le (((var 9)*(var 5))*((var 9)*(var 5))*pw ((var 1)*(var 4)) (two*(var 12))*pw (var 11) (two*(var 13)))
        (((var 8)*(var 7)*(var 6))*((var 8)*(var 7)*(var 6))*pw (var 10) (two*(var 13))*pw ((var 2)*(var 3)) (two*(var 12)))) :=
  closeUniv 14 (.impI (.impI (.impI (.impI
    (combined_point_budget _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianTravelResidualClearing
