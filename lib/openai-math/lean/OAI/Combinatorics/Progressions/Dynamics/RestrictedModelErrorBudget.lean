/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.ModelTransferPrecision
import OAI.Combinatorics.Progressions.Probability.RestrictedWeightedLawModeledTransfer

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem restricted_model_error_mean_le
    {H Ω I : Type*} [Fintype H] [Fintype I]
    (law : FiniteProbabilityWeights H) (productive : Finset H)
    (A B : H → (Ω → ℂ) →ₗ[ℂ] ℂ) (J : I → Ω → ℂ) (c : I → ℂ) (e : Ω → ℂ)
    {M η ε : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hc : (∑ i, ‖c i‖) ≤ M)
    (hatom : ∀ h ∈ productive, ∀ i, ‖A h (J i) - B h (J i)‖ ≤ η)
    (hambient : ∀ h ∈ productive, ‖A h e‖ ≤ ε)
    (hlocal : law.mean (fun h => if h ∈ productive then ‖B h e‖ else 0) ≤ ε) :
    law.mean (fun h => if h ∈ productive then
      (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) + ‖A h e‖ + ‖B h e‖ else 0) ≤
        M * η + 2 * ε := by
  have hM : 0 ≤ M := (Finset.sum_nonneg (fun i _ => norm_nonneg (c i))).trans hc
  have hb := law.mean_mono (fun h => show
      (if h ∈ productive then
        (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) + ‖A h e‖ + ‖B h e‖ else 0) ≤
      M * η + ε + (if h ∈ productive then ‖B h e‖ else 0) from by
    by_cases hh : h ∈ productive
    · simp only [ite_eq_left hh]
      have ha : (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) ≤ M * η := by
        calc
          _ ≤ ∑ i, ‖c i‖ * η := Finset.sum_le_sum
            (fun i _ => mul_le_mul_of_nonneg_left (hatom h hh i) (norm_nonneg _))
          _ = (∑ i, ‖c i‖) * η := (Finset.sum_mul _ _ _).symm
          _ ≤ M * η := mul_le_mul_of_nonneg_right hc hη
      linarith [hambient h hh]
    · simp only [ite_eq_right hh, add_zero]
      exact add_nonneg (mul_nonneg hM hη) hε)
  rw [law.mean_add, law.mean_const] at hb
  linarith

theorem restricted_model_exponential_error_budget {ρ τ R T Q E u : ℝ}
    (hT : 0 ≤ T) (hρ : Real.exp (-R) ≤ ρ) (hτ : Real.exp (-T) ≤ τ)
    (hu : R + T + 6 ≤ u) (hE : Q + (T + R) + 8 ≤ E) :
    Real.exp Q * Real.exp (-E) + 2 * Real.exp (-u) ≤ τ * ρ / 8 := by
  have hprod : Real.exp (-(T + R)) ≤ τ * ρ := by
    rw [neg_add, Real.exp_add]
    exact mul_le_mul hτ hρ (Real.exp_nonneg _) ((Real.exp_nonneg _).trans hτ)
  have ha := model_transfer_atom_precision hprod (le_refl (Real.exp Q)) hE
  have he := (model_transfer_residual_precision hT hρ hτ hu).1
  nlinarith

end Erdos3

end

end OAI
