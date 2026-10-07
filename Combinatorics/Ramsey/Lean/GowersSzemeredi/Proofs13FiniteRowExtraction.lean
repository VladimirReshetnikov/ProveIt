import GowersSzemeredi.Proofs13FiniteStageBudgets
import GowersSzemeredi.Proofs13SmallRowScale
import GowersSzemeredi.Proofs13AllDensityExtraction

/-! All-scale construction for Lemma 13.6 from the preceding extraction
data, at the Fourier cutoff specified in the paper's proof. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem lemma_13_6_prime_large_case {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D)
    (h135 : IsStage135Data S D E)
    (hlarge : 1 ≤ section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha))) :
    ∃ F : Stage136Data N, IsStage136Data S D E F ∧ F.R.length ≤ E.Q.length := by
  obtain ⟨m, hm, hsize, hupper, hlower, hbohr⟩ := section13_finite_integer_budgets
    S.alpha_pos S.alpha_at_most_one N D.q D.m D.P.length E.Q.length
    (by have := (Fact.out : N.Prime).two_le; omega) h134.1 h134.2.2.2.2.1
    h134.2.2.2.2.2.1 h134.2.2.2.2.2.2.1 h135.2.2.2.1 hlarge
  exact lemma_13_6_from_initial_stages_all_densities S D E m h134 h135
    hm hsize hupper hlower hbohr

theorem lemma_13_6_prime {N : Nat} [NeZero N] (hprime : N.Prime)
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D)
    (h135 : IsStage135Data S D E) :
    ∃ F : Stage136Data N, IsStage136Data S D E F := by
  letI : Fact N.Prime := ⟨hprime⟩
  by_cases hs : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ 1
  · exact lemma_13_6_small_row_scale S D E h135 hs
  · obtain ⟨F, hF, _⟩ := lemma_13_6_prime_large_case S D E h134 h135 (lt_of_not_ge hs).le
    exact ⟨F, hF⟩

end LeanProofs.GowersSzemeredi
