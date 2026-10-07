import GowersSzemeredi.Proofs13TenRowBudgets
import GowersSzemeredi.Proofs13SmallRowScale
import GowersSzemeredi.Proofs13AllDensityExtraction

/-! Improve Lemma 13.6's length exponent from 13Q to 10Q, preserving its
common step, all density conclusions, and the upper length when Q is nonempty. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem lemma_13_6_improved_length {N : Nat} [NeZero N] (hprime : N.Prime)
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D)
    (h135 : IsStage135Data S D E) :
    ∃ F : Stage136Data N, IsStage136Data S D E F ∧
      section13Zeta S.alpha / 2 *
        (N : Real) ^ ((1 : Real) / (2 : Real) ^ (10 * section13Q S.alpha)) ≤ F.R.length ∧
      F.R.length ≤ max 1 E.Q.length := by
  letI : Fact N.Prime := ⟨hprime⟩
  have hN : 1 ≤ N := by have := hprime.two_le; omega
  have htarget := section13_row_target_antitone S.alpha_pos N hN (by norm_num : (10 : Real) ≤ 13)
  by_cases hs : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (10 * section13Q S.alpha)) ≤ 1
  · obtain ⟨F, hF, hlen⟩ := lemma_13_6_small_row_scale_with_length S D E h135 (htarget.trans hs)
    refine ⟨F, hF, ?_, ?_⟩
    · simpa only [hlen, Nat.cast_one] using hs
    · rw [hlen]
      exact le_max_left _ _
  · obtain ⟨m, hm, hsize, hupper, hlower, hbohr⟩ := section13_ten_integer_budgets
      S.alpha_pos S.alpha_at_most_one N D.q D.m D.P.length E.Q.length hN h134.1
      h134.2.2.2.2.1 h134.2.2.2.2.2.1 h134.2.2.2.2.2.2.1 h135.2.2.2.1 (lt_of_not_ge hs).le
    obtain ⟨F, hF, hmR, hRupper⟩ := lemma_13_6_from_initial_stages_all_densities_with_length
      S D E m h134 h135 hm hsize hupper (htarget.trans hlower) hbohr
    exact ⟨F, hF, hlower.trans (Nat.cast_le.mpr hmR), hRupper.trans (le_max_right _ _)⟩

/-- For a nonempty preceding height progression, retain the upper geometry
needed by the later row and coefficient extractions at every scale. -/
theorem lemma_13_6_of_nonempty_height_progression {N : Nat} [NeZero N] (hprime : N.Prime)
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D)
    (h135 : IsStage135Data S D E) (hQ : 0 < E.Q.length) :
    ∃ F : Stage136Data N, IsStage136Data S D E F ∧
      section13Zeta S.alpha / 2 *
        (N : Real) ^ ((1 : Real) / (2 : Real) ^ (10 * section13Q S.alpha)) ≤ F.R.length ∧
      F.R.length ≤ E.Q.length := by
  obtain ⟨F, hF, hlower, hupper⟩ := lemma_13_6_improved_length hprime S D E h134 h135
  exact ⟨F, hF, hlower, by simpa only [max_eq_right (by omega : 1 ≤ E.Q.length)] using hupper⟩

end LeanProofs.GowersSzemeredi
