import Surreal.Algebra.AnalyticTaylor
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

/-!
# Formal Taylor composition at the correct ordinary centers

For `trigonometry:prop:lift`, the inner series must have its ordinary constant
removed, and the outer Taylor series must be centered at that ordinary value.
Coefficient induction proves the identity using the ordinary analytic chain
rule and Mathlib's native formal substitution chain rule. No composition of
unrestricted nonzero-constant formal series is used.
-/

namespace Surreal.Analytic

open Filter Topology

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [CharZero K]

omit [CompleteSpace K] [CharZero K] in
/-- Remove the inner ordinary value before formal substitution. -/
def centeredTaylorSeries (g : K → K) (c : K) : PowerSeries K :=
  taylorSeries g c - PowerSeries.C (g c)

omit [CompleteSpace K] [CharZero K] in
@[simp] theorem constantCoeff_centeredTaylorSeries (g : K → K) (c : K) :
    PowerSeries.constantCoeff (centeredTaylorSeries g c) = 0 := by
  simp [centeredTaylorSeries]

omit [CompleteSpace K] in
/-- Subtracting the ordinary value leaves the formal derivative unchanged. -/
theorem derivative_centeredTaylorSeries (g : K → K) (c : K) :
    PowerSeries.derivative K (centeredTaylorSeries g c) = taylorSeries (deriv g) c := by
  simp only [centeredTaylorSeries, map_sub, PowerSeries.derivative_C, sub_zero,
    taylorSeries_deriv]

private theorem taylorSeries_deriv_comp {f g : K → K} {c : K}
    (hf : AnalyticAt K f (g c)) (hg : AnalyticAt K g c) :
    taylorSeries (deriv (f ∘ g)) c =
      taylorSeries (deriv f ∘ g) c * taylorSeries (deriv g) c := by
  have he : deriv (f ∘ g) =ᶠ[𝓝 c] (deriv f ∘ g) * deriv g := by
    filter_upwards [hg.continuousAt.tendsto.eventually hf.eventually_analyticAt,
      hg.eventually_analyticAt] with x hfx hgx
    exact deriv_comp x hfx.differentiableAt hgx.differentiableAt
  rw [taylorSeries_congr he, taylorSeries_mul (hf.deriv.comp hg) hg.deriv]

/-- The Taylor series of an analytic composite is native zero-constant formal substitution. -/
theorem taylorSeries_comp {f g : K → K} {c : K}
    (hf : AnalyticAt K f (g c)) (hg : AnalyticAt K g c) :
    taylorSeries (f ∘ g) c =
      (taylorSeries f (g c)).subst (centeredTaylorSeries g c) := by
  ext n
  induction n using Nat.strong_induction_on generalizing f g with
  | h n ih =>
    have hB : PowerSeries.HasSubst (centeredTaylorSeries g c) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_centeredTaylorSeries g c)
    cases n with
    | zero =>
      rw [PowerSeries.coeff_subst' hB]
      rw [finsum_eq_single _ 0]
      · simp [Function.comp_def]
      · intro n hn
        simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
          constantCoeff_centeredTaylorSeries, zero_pow hn, smul_zero]
    | succ n =>
      have hn : (n + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      apply mul_right_cancel₀ hn
      rw [← PowerSeries.coeff_derivative, ← PowerSeries.coeff_derivative,
        ← taylorSeries_deriv, taylorSeries_deriv_comp hf hg,
        PowerSeries.derivative_subst K hB, ← taylorSeries_deriv,
        derivative_centeredTaylorSeries, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro ij hij
      have hs := Finset.mem_antidiagonal.mp hij
      rw [ih ij.1 (by omega) hf.deriv hg]

end

end Surreal.Analytic
