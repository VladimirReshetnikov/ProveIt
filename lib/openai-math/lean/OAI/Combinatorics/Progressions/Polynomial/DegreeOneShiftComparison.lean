import OAI.Combinatorics.Progressions.Estimates.CyclicBilinearBound

namespace OAI

section

namespace Erdos3

theorem exists_degree_one_shift_comparison {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (p : ℝ), 2 ≤ p →
      ∀ A B J : ZMod N → ℝ,
      (∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p) → (∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p) →
      (∀ r, 0 ≤ J r ∧ J r ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} 1 N ((p + 2) ^ C) (Real.exp (-((p + 2) ^ C))) A B →
      ∃ E : Finset (ZMod N), (E.card : ℝ) ≤ Real.exp (-p) * N ∧
        CyclicNiltestShiftBound.{0} 0 N p (Real.exp (-p))
          (fun r => A r - (1 + epsilon) * B r) J E := by
  obtain ⟨C, hC, hbilinear⟩ := CellRefinement.exists_degree_one_bilinear_bound hepsilon hepsilon1
  refine ⟨C, hC, ?_⟩
  intro N hN p hp A B J hA hB hJ hcompare
  obtain ⟨E, hE, hshifts⟩ := exists_small_bad_shift_set
    (fun r => A r - (1 + epsilon) * B r) J (by linarith) hJ
    (hbilinear N p hp A B hA hB hcompare)
  refine ⟨E, ?_, cyclicNiltestShiftBound_zero_of_constants _ _ E hshifts⟩
  simpa using hE

end Erdos3

end

end OAI
