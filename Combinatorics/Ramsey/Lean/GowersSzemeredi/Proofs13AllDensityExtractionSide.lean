import GowersSzemeredi.Proofs13AllDensityExtraction
import GowersSzemeredi.Proofs13LargeScaleBudgets

/-! Stage 13.6 without an ambient-density restriction. Adaptive edge fibre
normalization preserves every previously checked constant and exponent.

Moved here from `Proofs13AllDensityExtraction`, which keeps only what the final
route uses. -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Construct Stage 13.6 from the initial stages and numerical budgets at
all densities allowed by Section13Context. -/
theorem lemma_13_6_from_initial_stages_all_densities_with_length {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N) (m : Nat)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D)
    (h135 : IsStage135Data S D E)
    (hm : 0 < m) (hsize : m * m ≤ N) (hupper : m + 1 ≤ E.Q.length)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m)
    (hbudget : (D.P.length : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * D.q))) ≤
      section10Zeta (S.alpha ^ 32 / 16) / m) :
    ∃ F : Stage136Data N, IsStage136Data S D E F ∧ m ≤ F.R.length ∧ F.R.length ≤ E.Q.length :=
  lemma_13_6_from_initial_stages_at S D E m _ h134 h135 h135.2.2.2.2.1 hm hsize hupper hlower
    hbudget

theorem lemma_13_6_from_initial_stages_all_densities {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N) (m : Nat)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D)
    (h135 : IsStage135Data S D E)
    (hm : 0 < m) (hsize : m * m ≤ N) (hupper : m + 1 ≤ E.Q.length)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m)
    (hbudget : (D.P.length : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * D.q))) ≤
      section10Zeta (S.alpha ^ 32 / 16) / m) :
    ∃ F : Stage136Data N, IsStage136Data S D E F ∧ F.R.length ≤ E.Q.length  := by
  obtain ⟨F, hF, _, hupper⟩ := lemma_13_6_from_initial_stages_all_densities_with_length
    S D E m h134 h135 hm hsize hupper hlower hbudget
  exact ⟨F, hF, hupper⟩

end LeanProofs.GowersSzemeredi

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
