import GowersSzemeredi.Proofs13AllDensityExtraction
import GowersSzemeredi.Proofs13LargeScaleBudgets

/-! Declarations of `Proofs13AllDensityExtraction` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- For every fixed positive density at most one, the numerical budgets
are automatic at sufficiently large prime moduli. -/
theorem lemma_13_6_large_N_all_densities {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    ∃ N₀ : Nat, ∀ (N : Nat) [Fact N.Prime]
      (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N),
      S.alpha = alpha → N₀ ≤ N →
      IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D →
      IsStage135Data S D E →
      ∃ F : Stage136Data N, IsStage136Data S D E F ∧ F.R.length ≤ E.Q.length := by
  obtain ⟨N₀, hN₀⟩ := section13_uniform_integer_budgets hα hαone
  refine ⟨N₀, fun N _ S D E hS hN h134 h135 => ?_⟩
  have hb := hN₀ N hN D.q D.m D.P.length E.Q.length h134.1
    (by simpa only [hS] using h134.2.2.2.2.1)
    (by simpa only [hS] using h134.2.2.2.2.2.1)
    h134.2.2.2.2.2.2.1 h135.2.2.2.1
  rw [← hS] at hb
  obtain ⟨m, hm, hsize, hupper, hlower, hbudget, _⟩ := hb
  exact lemma_13_6_from_initial_stages_all_densities S D E m
    h134 h135 hm hsize hupper hlower hbudget

end LeanProofs.GowersSzemeredi
