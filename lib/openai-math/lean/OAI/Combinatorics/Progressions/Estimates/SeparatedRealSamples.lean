import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem real_interval_cover_measure_le (t : Finset ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (⋃ y ∈ t, Set.Ioo (y - r) (y + r)) ≤ 2 * (t.card : ℝ) * r := by
  apply (measureReal_biUnion_finset_le t (fun y => Set.Ioo (y - r) (y + r))).trans
  have hlen (y : ℝ) : volume.real (Set.Ioo (y - r) (y + r)) = 2 * r := by
    rw [Real.volume_real_Ioo_of_le (by linarith)]
    ring
  simp only [hlen, Finset.sum_const, nsmul_eq_mul]
  ring_nf
  exact le_rfl

theorem exists_separated_real_samples (s : Set ℝ) {r : ℝ} (hr : 0 < r) (n : ℕ)
    (hlarge : 2 * (n : ℝ) * r < volume.real s) :
    ∃ t : Finset ℝ, t.card = n ∧ (↑t : Set ℝ) ⊆ s ∧
      ∀ x ∈ t, ∀ y ∈ t, x ≠ y → r ≤ |x - y| := by
  classical
  induction n with
  | zero => exact ⟨∅, rfl, by simp, by simp⟩
  | succ n ih =>
    have hsmall : 2 * (n : ℝ) * r < volume.real s := by
      push_cast at hlarge
      nlinarith
    obtain ⟨t, hcard, hts, hsep⟩ := ih hsmall
    let cover := ⋃ y ∈ t, Set.Ioo (y - r) (y + r)
    have hfinite : volume cover ≠ ⊤ := by
      apply measure_biUnion_ne_top t.finite_toSet
      intro y _
      simp only [Real.volume_Ioo, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]
    have hnot : ¬s ⊆ cover := by
      intro hsub
      have h := (measureReal_mono hsub hfinite).trans (real_interval_cover_measure_le t hr.le)
      rw [hcard] at h
      linarith
    obtain ⟨x, hxs, hxc⟩ := Set.not_subset.mp hnot
    have hfar (y : ℝ) (hy : y ∈ t) : r ≤ |x - y| := by
      by_contra! h
      have hxy := abs_lt.mp h
      apply hxc
      exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, ⟨by linarith, by linarith⟩⟩⟩
    have hxt : x ∉ t := by
      intro hx
      have h := hfar x hx
      simp only [sub_self, abs_zero] at h
      linarith
    refine ⟨insert x t, by rw [Finset.card_insert_of_notMem hxt, hcard], ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxs
      · exact hts hy
    · intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hax | hat
      · subst a
        rcases Finset.mem_insert.mp hb with rfl | hbt
        · exact False.elim (hab rfl)
        · exact hfar b hbt
      · rcases Finset.mem_insert.mp hb with hbx | hbt
        · subst b
          simpa only [abs_sub_comm] using hfar a hat
        · exact hsep a hat b hbt hab

end Erdos3

end

end OAI
