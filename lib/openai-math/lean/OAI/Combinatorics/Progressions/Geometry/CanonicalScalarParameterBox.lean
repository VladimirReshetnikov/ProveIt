import OAI.Combinatorics.Progressions.Linear.CanonicalJointFrameGeometry

namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def canonicalScalarParameterRadius (L : ℝ) : ℕ := ⌈2 * L⌉₊

theorem canonicalScalarParameterRadius_bounds {L : ℝ} (hL : 1 ≤ L) :
    0 < canonicalScalarParameterRadius L ∧
      2 * L ≤ (canonicalScalarParameterRadius L : ℝ) ∧
      (canonicalScalarParameterRadius L : ℝ) ≤ 3 * L := by
  have hceil : 2 * L ≤ (⌈2 * L⌉₊ : ℝ) := Nat.le_ceil _
  have hupper := Nat.ceil_lt_add_one (show 0 ≤ 2 * L by linarith)
  refine ⟨?_, hceil, ?_⟩
  · have : (0 : ℝ) < canonicalScalarParameterRadius L :=
      (by linarith : 0 < 2 * L).trans_le hceil
    exact_mod_cast this
  · change (⌈2 * L⌉₊ : ℝ) ≤ 3 * L
    linarith

theorem canonicalScalarParameterSite_bounds {d : ℕ} (hd : 2 ≤ d)
    {L : ℝ} (_hL : 1 ≤ L) (P : Fin d → ℕ)
    (hlo : ∀ j, L ≤ (P j : ℝ)) (hhi : ∀ j, (P j : ℝ) ≤ 2 * L) :
    0 ≤ (∑ j, (P j : ℝ)) ∧ L ≤ (∑ j, (P j : ℝ)) ∧
      (∑ j, (P j : ℝ)) ≤ 2 * (d : ℝ) * L := by
  refine ⟨Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _), ?_, ?_⟩
  · let j : Fin d := ⟨0, by omega⟩
    exact (hlo j).trans (Finset.single_le_sum
      (fun _ _ => Nat.cast_nonneg (α := ℝ) _) (Finset.mem_univ j))
  · have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hhi j)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_left_comm (d : ℝ) 2 L, mul_assoc] using h

theorem canonicalScalarParameterBox_bounds {d : ℕ} (hd : 2 ≤ d)
    {L : ℝ} (hL : 1 ≤ L) (P : Fin d → ℕ)
    (hlo : ∀ j, L ≤ (P j : ℝ)) (hhi : ∀ j, (P j : ℝ) ≤ 2 * L) :
    (∀ j, (0 : ℤ) < (P j : ℤ)) ∧
    0 < L ∧
    (∀ j, L ≤ (((P j : ℤ) - 0 : ℤ) : ℝ)) ∧
    (∀ j, (P j : ℤ) - 0 ≤ (canonicalScalarParameterRadius L : ℤ)) ∧
    (canonicalScalarParameterRadius L : ℝ) ≤ 3 * L ∧
    1 * L ≤ L ∧
    |(0 : ℝ) / L| ≤ 2 ∧
    (∀ j, |(((P j : ℤ) : ℝ)) / L| ≤ 2) ∧
    0 ≤ (∑ j, (P j : ℝ)) ∧ L ≤ (∑ j, (P j : ℝ)) ∧
      (∑ j, (P j : ℝ)) ≤ 2 * (d : ℝ) * L := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hrad := canonicalScalarParameterRadius_bounds hL
  refine ⟨?_, hLp, ?_, ?_, hrad.2.2, by simp, by norm_num, ?_,
    canonicalScalarParameterSite_bounds hd hL P hlo hhi⟩
  · intro j
    exact_mod_cast hLp.trans_le (hlo j)
  · simpa only [sub_zero, Int.cast_natCast] using hlo
  · intro j
    have h := (hhi j).trans hrad.2.1
    rw [sub_zero]
    exact_mod_cast h
  · intro j
    rw [Int.cast_natCast, abs_div, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hLp]
    exact (div_le_iff₀ hLp).mpr (hhi j)

end Erdos3.BooleanCubeKernel

end

end OAI
