import OAI.Combinatorics.Progressions.Linear.CanonicalJointFrameGeometry

namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def comparableScalarParameterRadius (r L : ℝ) : ℕ := ⌈r * L⌉₊

theorem comparableScalarParameterRadius_bounds {r L : ℝ} (hr : 2 ≤ r) (hL : 1 ≤ L) :
    0 < comparableScalarParameterRadius r L ∧
      r * L ≤ (comparableScalarParameterRadius r L : ℝ) ∧
      (comparableScalarParameterRadius r L : ℝ) ≤ (r + 1) * L := by
  have hceil : r * L ≤ (⌈r * L⌉₊ : ℝ) := Nat.le_ceil _
  have hupper := Nat.ceil_lt_add_one (show 0 ≤ r * L by positivity)
  refine ⟨?_, hceil, ?_⟩
  · have : (0 : ℝ) < comparableScalarParameterRadius r L :=
      (by positivity : 0 < r * L).trans_le hceil
    exact_mod_cast this
  · change (⌈r * L⌉₊ : ℝ) ≤ (r + 1) * L
    nlinarith

theorem comparableScalarParameterSite_bounds {d : ℕ} (hd : 2 ≤ d)
    {r L : ℝ} (_hr : 2 ≤ r) (_hL : 1 ≤ L) (P : Fin d → ℕ)
    (hlo : ∀ j, L ≤ (P j : ℝ)) (hhi : ∀ j, (P j : ℝ) ≤ r * L) :
    0 ≤ (∑ j, (P j : ℝ)) ∧ L ≤ (∑ j, (P j : ℝ)) ∧
      (∑ j, (P j : ℝ)) ≤ r * (d : ℝ) * L := by
  refine ⟨Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _), ?_, ?_⟩
  · let j : Fin d := ⟨0, by omega⟩
    exact (hlo j).trans (Finset.single_le_sum
      (fun _ _ => Nat.cast_nonneg (α := ℝ) _) (Finset.mem_univ j))
  · have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hhi j)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_left_comm (d : ℝ) r L, mul_assoc] using h

theorem comparableScalarParameterBox_bounds {d : ℕ} (hd : 2 ≤ d)
    {r L : ℝ} (hr : 2 ≤ r) (hL : 1 ≤ L) (P : Fin d → ℕ)
    (hlo : ∀ j, L ≤ (P j : ℝ)) (hhi : ∀ j, (P j : ℝ) ≤ r * L) :
    (∀ j, (0 : ℤ) < (P j : ℤ)) ∧
    0 < L ∧
    (∀ j, L ≤ (((P j : ℤ) - 0 : ℤ) : ℝ)) ∧
    (∀ j, (P j : ℤ) - 0 ≤ (comparableScalarParameterRadius r L : ℤ)) ∧
    (comparableScalarParameterRadius r L : ℝ) ≤ (r + 1) * L ∧
    1 * L ≤ L ∧
    |(0 : ℝ) / L| ≤ r ∧
    (∀ j, |(((P j : ℤ) : ℝ)) / L| ≤ r) ∧
    0 ≤ (∑ j, (P j : ℝ)) ∧ L ≤ (∑ j, (P j : ℝ)) ∧
      (∑ j, (P j : ℝ)) ≤ r * (d : ℝ) * L := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hrad := comparableScalarParameterRadius_bounds hr hL
  refine ⟨?_, hLp, ?_, ?_, hrad.2.2, by simp, by simpa using (by linarith : (0 : ℝ) ≤ r), ?_,
    comparableScalarParameterSite_bounds hd hr hL P hlo hhi⟩
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

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

theorem indexedComparableScalarParameterSite_bounds {d : ℕ} (hd : 2 ≤ d)
    {K : Type*} [Fintype K] (hK : Fintype.card K = d)
    {r L : ℝ} (_hr : 2 ≤ r) (_hL : 1 ≤ L) (P : K → ℕ)
    (hlo : ∀ j, L ≤ (P j : ℝ)) (hhi : ∀ j, (P j : ℝ) ≤ r * L) :
    0 ≤ (∑ j, (P j : ℝ)) ∧ L ≤ (∑ j, (P j : ℝ)) ∧
      (∑ j, (P j : ℝ)) ≤ r * (d : ℝ) * L := by
  refine ⟨Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _), ?_, ?_⟩
  · have hnonempty : Nonempty K := Fintype.card_pos_iff.mp (by omega)
    let j : K := Classical.choice hnonempty
    exact (hlo j).trans (Finset.single_le_sum
      (fun _ _ => Nat.cast_nonneg (α := ℝ) _) (Finset.mem_univ j))
  · have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hhi j)
    simpa only [Finset.sum_const, Finset.card_univ, hK,
      nsmul_eq_mul, mul_left_comm (d : ℝ) r L, mul_assoc] using h

theorem indexedComparableScalarParameterBox_bounds {d : ℕ} (hd : 2 ≤ d)
    {K : Type*} [Fintype K] (hK : Fintype.card K = d)
    {r L : ℝ} (hr : 2 ≤ r) (hL : 1 ≤ L) (P : K → ℕ)
    (hlo : ∀ j, L ≤ (P j : ℝ)) (hhi : ∀ j, (P j : ℝ) ≤ r * L) :
    (∀ j, (0 : ℤ) < (P j : ℤ)) ∧
    0 < L ∧
    (∀ j, L ≤ (((P j : ℤ) - 0 : ℤ) : ℝ)) ∧
    (∀ j, (P j : ℤ) - 0 ≤ (comparableScalarParameterRadius r L : ℤ)) ∧
    (comparableScalarParameterRadius r L : ℝ) ≤ (r + 1) * L ∧
    1 * L ≤ L ∧
    |(0 : ℝ) / L| ≤ r ∧
    (∀ j, |(((P j : ℤ) : ℝ)) / L| ≤ r) ∧
    0 ≤ (∑ j, (P j : ℝ)) ∧ L ≤ (∑ j, (P j : ℝ)) ∧
      (∑ j, (P j : ℝ)) ≤ r * (d : ℝ) * L := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hrad := comparableScalarParameterRadius_bounds hr hL
  refine ⟨?_, hLp, ?_, ?_, hrad.2.2, by simp, by simpa using (by linarith : (0 : ℝ) ≤ r), ?_,
    indexedComparableScalarParameterSite_bounds hd hK hr hL P hlo hhi⟩
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
