/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.RestrictedModelErrorBudget

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_finiteLaw_forecast_model_transfer
    {H Ω U I : Type*} [Fintype H] [Fintype Ω] [Fintype U] [Fintype I]
    (law : FiniteProbabilityWeights H) (productive : Finset H)
    (localLaw : H → FiniteProbabilityWeights U) (ψ : H → U → Ω)
    (forecast : H → Ω → ℝ) (v : Ω → ℝ)
    (models : I → Ω → ℂ) (coeff : I → ℂ) (err : Ω → ℂ)
    (hmodel : (fun u => (v u : ℂ)) = (∑ i, coeff i • models i) + err)
    {τ ρ R T Q E u : ℝ} (hT : 0 ≤ T)
    (hρ : Real.exp (-R) ≤ ρ) (hτ : Real.exp (-T) ≤ τ)
    (hu : R + T + 6 ≤ u) (hE : Q + (T + R) + 8 ≤ E)
    (hc : (∑ i, ‖coeff i‖) ≤ Real.exp Q)
    (hmass : τ ≤ law.mass productive)
    (hatom : ∀ h ∈ productive, ∀ i,
      ‖(𝔼 x, (forecast h x : ℂ) * models i x) -
        (localLaw h).complexMean (fun a => models i (ψ h a))‖ ≤ Real.exp (-E))
    (hambient : ∀ h ∈ productive,
      ‖𝔼 x, (forecast h x : ℂ) * err x‖ ≤ Real.exp (-u))
    (hlocal : law.mean (fun h => if h ∈ productive then
      ‖(localLaw h).complexMean (fun a => err (ψ h a))‖ else 0) ≤ Real.exp (-u))
    (hscore : ∀ h ∈ productive, ρ ≤ (localLaw h).mean (fun a => v (ψ h a))) :
    ∃ h ∈ productive, ρ / 2 ≤ 𝔼 x, forecast h x * v x := by
  let A₀ := fun h => finiteWeightedTest id (fun x => (forecast h x : ℂ))
  let B₀ := fun h => finiteProbabilityTest (localLaw h) (ψ h)
  have hb := restricted_model_error_mean_le law productive A₀ B₀ models coeff err
    (Real.exp_nonneg (-E)) (Real.exp_nonneg (-u)) hc hatom hambient hlocal
  have hbudget := restricted_model_exponential_error_budget hT hρ hτ hu hE
  let A := fun h => if h ∈ productive then A₀ h else 0
  let B := fun h => if h ∈ productive then B₀ h else 0
  have he : law.mean (fun h =>
      (∑ i, ‖coeff i‖ * ‖A h (models i) - B h (models i)‖) +
      ‖A h err‖ + ‖B h err‖) ≤ τ * ρ / 8 := by
    apply le_trans _ (hb.trans hbudget)
    apply law.mean_mono
    intro h
    by_cases hh : h ∈ productive
    · simp only [A, B, ite_eq_left hh, le_refl]
    · simp [A, B, hh]
  have hs : ∀ h ∈ productive, ρ ≤ (B h (fun x => (v x : ℂ))).re := by
    intro h hh
    simpa only [B, B₀, ite_eq_left hh, finiteProbabilityTest_real] using hscore h hh
  obtain ⟨h, hh, htransfer⟩ := exists_productive_averaged_model_transfer law productive
    A B (fun x => (v x : ℂ)) err models coeff hmodel
    ((Real.exp_pos _).trans_le hτ) ((Real.exp_pos _).trans_le hρ) hmass he hs
  exact ⟨h, hh, by simpa only [A, A₀, ite_eq_left hh, finiteWeightedTest_real, id_eq] using htransfer⟩

end Erdos3

end

end OAI
