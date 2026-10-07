import Mathlib

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def spectrumTail {K : Type*} [Fintype K] [DecidableEq K]
    (S : Finset K) (f : K → ℝ) : ℝ := ∑ k, if k ∈ S then 0 else f k

theorem spectrumTail_le_card {K : Type*} [Fintype K] [DecidableEq K]
    (S : Finset K) (f : K → ℝ) {w : ℝ} (hw : 0 ≤ w)
    (h : ∀ k, k ∉ S → f k ≤ w) : spectrumTail S f ≤ Fintype.card K * w := by
  calc
    _ ≤ ∑ _k : K, w := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k ∈ S <;> simp only [hk, ite_true, ite_false]
      · exact hw
      · exact h k hk
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem spectrumTail_step {K : Type*} [Fintype K] [DecidableEq K]
    (S T : Finset K) (f : K → ℝ) (hf : ∀ k, 0 ≤ f k) {w : ℝ} (hw : 0 ≤ w)
    (h : ∀ k, k ∉ S → f k ≤ w) :
    spectrumTail S f ≤ T.card * w + spectrumTail T f := by
  have hp (k : K) : (if k ∈ S then 0 else f k) ≤
      (if k ∈ T then w else 0) + (if k ∈ T then 0 else f k) := by
    by_cases hs : k ∈ S <;> by_cases ht : k ∈ T <;>
      simp only [hs, ht, ite_true, ite_false, zero_add, add_zero]
    · exact hw
    · exact hf k
    · exact h k hs
    · exact le_rfl
  calc
    _ ≤ ∑ k, ((if k ∈ T then w else 0) + (if k ∈ T then 0 else f k)) :=
      Finset.sum_le_sum (fun k _ => hp k)
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, spectrumTail]

theorem spectrumTail_levels {K : Type*} [Fintype K] [DecidableEq K]
    (S : ℕ → Finset K) (f : K → ℝ) (hf : ∀ k, 0 ≤ f k)
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (h : ∀ i k, k ∉ S i → f k ≤ w i) (n : ℕ) :
    spectrumTail (S 0) f ≤ (∑ i ∈ Finset.range n, (S (i + 1)).card * w i) +
      Fintype.card K * w n := by
  induction n generalizing S w with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty, zero_add] using
      spectrumTail_le_card (S 0) f (hw 0) (h 0)
  | succ n ih =>
      have hstep := spectrumTail_step (S 0) (S 1) f hf (hw 0) (h 0)
      have htail := ih (fun i => S (i + 1)) (fun i => w (i + 1))
        (fun i => hw (i + 1)) (fun i => h (i + 1))
      calc
        _ ≤ (S 1).card * w 0 + ((∑ i ∈ Finset.range n, (S (i + 1 + 1)).card * w (i + 1)) +
            Fintype.card K * w (n + 1)) := hstep.trans (add_le_add le_rfl htail)
        _ = _ := by rw [Finset.sum_range_succ']; ring

theorem spectrumTail_geometric {K : Type*} [Fintype K] [DecidableEq K]
    (S : ℕ → Finset K) (f : K → ℝ) (hf : ∀ k, 0 ≤ f k)
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (h : ∀ i k, k ∉ S i → f k ≤ w i)
    {C : ℝ} (hC : 0 ≤ C) (hlevel : ∀ i, (S (i + 1)).card * w i ≤ C * (1 / 2 : ℝ) ^ i)
    (n : ℕ) : spectrumTail (S 0) f ≤ 2 * C + Fintype.card K * w n := by
  apply (spectrumTail_levels S f hf w hw h n).trans
  refine add_le_add ?_ le_rfl
  calc
    _ ≤ ∑ i ∈ Finset.range n, C * (1 / 2 : ℝ) ^ i := Finset.sum_le_sum (fun i _ => hlevel i)
    _ = C * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := (Finset.mul_sum _ _ _).symm
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le n) hC
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_series_truncation_le {K : Type*} [Fintype K] [DecidableEq K]
    (S : Finset K) (c ψ : K → ℂ) (hψ : ∀ k, ‖ψ k‖ ≤ 1) :
    ‖(∑ k, c k * ψ k) - ∑ k ∈ S, c k * ψ k‖ ≤ spectrumTail S (fun k => ‖c k‖) := by
  have hid : (∑ k, c k * ψ k) - ∑ k ∈ S, c k * ψ k =
      ∑ k, if k ∈ S then 0 else c k * ψ k := by
    calc
      _ = ∑ k, (c k * ψ k - if k ∈ S then c k * ψ k else 0) := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_ite_mem, Finset.univ_inter]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k ∈ S <;> simp only [hk, ite_true, ite_false, sub_self, sub_zero]
  rw [hid]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k ∈ S
  · simp only [hk, ite_true, norm_zero, le_refl]
  · simp only [hk, ite_false, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hψ k)

theorem finite_series_norm_le {K : Type*} [Fintype K] (c ψ : K → ℂ)
    (hψ : ∀ k, ‖ψ k‖ ≤ 1) : ‖∑ k, c k * ψ k‖ ≤ ∑ k, ‖c k‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hψ k)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem spectrumTail_finite_levels {K : Type*} [Fintype K] [DecidableEq K]
    (S : ℕ → Finset K) (f : K → ℝ) (hf : ∀ k, 0 ≤ f k) (w : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i ≤ n, 0 ≤ w i) (h : ∀ i ≤ n, ∀ k, k ∉ S i → f k ≤ w i) :
    spectrumTail (S 0) f ≤ (∑ i ∈ Finset.range n, (S (i + 1)).card * w i) +
      Fintype.card K * w n := by
  have hs := spectrumTail_levels (fun i => S (min i n)) f hf (fun i => w (min i n))
    (fun i => hw _ (Nat.min_le_right i n)) (fun i => h _ (Nat.min_le_right i n)) n
  simp only [Nat.zero_min, Nat.min_self] at hs
  have heq : (∑ i ∈ Finset.range n, (S (min (i + 1) n)).card * w (min i n)) =
      ∑ i ∈ Finset.range n, (S (i + 1)).card * w i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Nat.min_eq_left (by omega : i + 1 ≤ n), Nat.min_eq_left (by omega : i ≤ n)]
  rwa [heq] at hs

theorem spectrumTail_finite_geometric {K : Type*} [Fintype K] [DecidableEq K]
    (S : ℕ → Finset K) (f : K → ℝ) (hf : ∀ k, 0 ≤ f k) (w : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i ≤ n, 0 ≤ w i) (h : ∀ i ≤ n, ∀ k, k ∉ S i → f k ≤ w i)
    {C : ℝ} (hC : 0 ≤ C)
    (hlevel : ∀ i < n, (S (i + 1)).card * w i ≤ C * (1 / 2 : ℝ) ^ i) :
    spectrumTail (S 0) f ≤ 2 * C + Fintype.card K * w n := by
  apply (spectrumTail_finite_levels S f hf w n hw h).trans
  refine add_le_add ?_ le_rfl
  calc
    _ ≤ ∑ i ∈ Finset.range n, C * (1 / 2 : ℝ) ^ i :=
      Finset.sum_le_sum (fun i hi => hlevel i (Finset.mem_range.mp hi))
    _ = C * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := (Finset.mul_sum _ _ _).symm
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le n) hC
    _ = _ := by ring

end Erdos3

end

end OAI
