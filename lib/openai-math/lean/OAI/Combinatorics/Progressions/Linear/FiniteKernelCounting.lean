import Mathlib.Data.Finset.Card
import OAI.Combinatorics.Progressions.Estimates.CountingDeficitDetection

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem subset_counting_error_scale {m n : ℕ} (hmn : m < n) {delta : ℝ} (hdelta : 0 ≤ delta) :
    (18 : ℝ) ^ m * delta ≤ ((18 : ℝ) ^ n * delta) / 18 := by
  calc
    (18 : ℝ) ^ m * delta = ((18 : ℝ) ^ (m + 1) * delta) / 18 := by rw [pow_succ]; ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hdelta)
      (by norm_num)

theorem finite_products_near_one_of_kernel_bound {I X : Type*}
    [DecidableEq I] [Fintype X] [Nonempty X] (s : ℕ) {delta : ℝ} (hdelta : 0 < delta)
    (F : I → X → ℝ) (hmean : ∀ i, |(𝔼 x, F i x) - 1| ≤ delta)
    (hkernel : ∀ (S : Finset I), S.card ≤ s → ∀ i j : I, i ∉ S → j ∉ S → i ≠ j →
      ∀ b : ℝ, (b = 1 ∨ b = 1 / 4) →
        countingKernelAverage b (fun x => ∏ k ∈ S, F k x) (F i) (F j) ≤ 1 + delta / 16)
    (T : Finset I) (hT : T.card ≤ s + 2) :
    |(𝔼 x, ∏ i ∈ T, F i x) - 1| ≤ (18 : ℝ) ^ T.card * delta := by
  induction T using Finset.strongInductionOn
  rename_i T ih
  rcases T.eq_empty_or_nonempty with rfl | hnonempty
  · simp only [Finset.prod_empty, Fintype.expect_const, sub_self, abs_zero,
      Finset.card_empty, pow_zero, one_mul]
    exact le_of_lt hdelta
  by_cases hsmall : T.card ≤ 1
  · obtain ⟨i, hi⟩ := hnonempty
    have heq : T = {i} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hi, fun j hj => Finset.card_le_one.mp hsmall j hj i hi⟩
    rw [heq]
    simp only [Finset.prod_singleton, Finset.card_singleton, pow_one]
    exact (hmean i).trans (by linarith)
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show 1 < T.card by omega)
  let S := (T.erase i).erase j
  have hj' : j ∈ T.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩
  have hSi : i ∉ S := by simp [S]
  have hSj : j ∉ S := by simp [S]
  have hSji : insert j S = T.erase i := Finset.insert_erase hj'
  have hSij : insert i S = T.erase j := by
    dsimp [S]
    rw [Finset.erase_right_comm, Finset.insert_erase (Finset.mem_erase.mpr ⟨hij, hi⟩)]
  have hform : T = insert i (insert j S) := by rw [hSji, Finset.insert_erase hi]
  have hScard : S.card ≤ s := by
    dsimp [S]
    rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem hi]
    omega
  have hproper (U : Finset I) (hU : U ⊂ T) :
      |(𝔼 x, ∏ k ∈ U, F k x) - 1| ≤ ((18 : ℝ) ^ T.card * delta) / 18 :=
    (ih U hU ((Finset.card_le_card (le_of_lt hU)).trans hT)).trans
      (subset_counting_error_scale (Finset.card_lt_card hU) (le_of_lt hdelta))
  have h00 := hproper S (lt_of_le_of_lt (Finset.erase_subset j (T.erase i))
    (Finset.erase_ssubset hi))
  have h10 : |(𝔼 x, (∏ k ∈ S, F k x) * F i x) - 1| ≤
      ((18 : ℝ) ^ T.card * delta) / 18 := by
    have h := hproper (insert i S) (by rw [hSij]; exact Finset.erase_ssubset hj)
    simpa only [Finset.prod_insert hSi, mul_comm] using h
  have h01 : |(𝔼 x, (∏ k ∈ S, F k x) * F j x) - 1| ≤
      ((18 : ℝ) ^ T.card * delta) / 18 := by
    have h := hproper (insert j S) (by rw [hSji]; exact Finset.erase_ssubset hi)
    simpa only [Finset.prod_insert hSj, mul_comm] using h
  have hprod (x : X) : (∏ k ∈ T, F k x) = (∏ k ∈ S, F k x) * F i x * F j x := by
    rw [hform, Finset.prod_insert (by simp [hij, hSi]), Finset.prod_insert hSj]
    ring
  by_contra! hbad
  simp only [hprod] at hbad
  obtain ⟨b, hb, hsurplus⟩ := exists_countingKernel_surplus
    (mul_pos (pow_pos (by norm_num) _) hdelta) (fun x => ∏ k ∈ S, F k x)
    (F i) (F j) h00 h10 h01 hbad
  have hu := hkernel S hScard i j hSi hSj hij b hb
  have hscale : delta ≤ (18 : ℝ) ^ T.card * delta := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_pow₀ (show (1 : ℝ) ≤ 18 by norm_num)) (le_of_lt hdelta)
  linarith

end Erdos3

end

end OAI
