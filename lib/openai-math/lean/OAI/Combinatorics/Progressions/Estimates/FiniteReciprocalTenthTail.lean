/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib

namespace OAI

section

namespace Erdos3

theorem one_sub_sum_mul_prod_one_add_le_one {ι : Type*} (S : Finset ι) (e : ι → ℝ)
    (he : ∀ i ∈ S, 0 ≤ e i) :
    (1 - ∑ i ∈ S, e i) * (∏ i ∈ S, (1 + e i)) ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have heS : ∀ i ∈ S, 0 ≤ e i := fun i hi => he i (Finset.mem_insert_of_mem hi)
    have hea := he a (Finset.mem_insert_self _ _)
    have hs := Finset.sum_nonneg heS
    have hp : 0 ≤ ∏ i ∈ S, (1 + e i) := Finset.prod_nonneg (fun i hi => by linarith [heS i hi])
    have hstep : (1 - (e a + ∑ i ∈ S, e i)) * (1 + e a) ≤ 1 - ∑ i ∈ S, e i := by
      nlinarith [mul_nonneg hea hs, sq_nonneg (e a)]
    rw [Finset.sum_insert ha, Finset.prod_insert ha, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right hstep hp).trans (ih heS)

theorem prod_one_add_le_one_add_twice_sum {ι : Type*} (S : Finset ι) (e : ι → ℝ)
    (he : ∀ i ∈ S, 0 ≤ e i) (hsmall : (∑ i ∈ S, e i) ≤ 1 / 2) :
    (∏ i ∈ S, (1 + e i)) ≤ 1 + 2 * ∑ i ∈ S, e i := by
  have h := one_sub_sum_mul_prod_one_add_le_one S e he
  have hs := Finset.sum_nonneg he
  have hp : 0 ≤ ∏ i ∈ S, (1 + e i) := Finset.prod_nonneg (fun i hi => by linarith [he i hi])
  have hp2 : (∏ i ∈ S, (1 + e i)) ≤ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hp2 hs]

theorem one_sub_sum_le_positive_prod {ι : Type*} (S : Finset ι) (f e : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) (he : ∀ i ∈ S, e i ∈ Set.Icc (0 : ℝ) 1)
    (hlower : ∀ i ∈ S, 1 - e i ≤ f i) :
    1 - ∑ i ∈ S, e i ≤ ∏ i ∈ S, f i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hfS := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have heS := fun i hi => he i (Finset.mem_insert_of_mem hi)
    have hlS := fun i hi => hlower i (Finset.mem_insert_of_mem hi)
    have hea := he a (Finset.mem_insert_self _ _)
    have hs := Finset.sum_nonneg (fun i hi => (heS i hi).1)
    have h₁ := mul_le_mul_of_nonneg_left (ih hfS heS hlS) (sub_nonneg.mpr hea.2)
    have h₂ := mul_le_mul_of_nonneg_right (hlower a (Finset.mem_insert_self _ _))
      (Finset.prod_nonneg hfS)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    nlinarith [mul_nonneg hea.1 hs]

theorem positive_prod_sub_one_le_twice_sum {ι : Type*} (S : Finset ι) (f e : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) (he : ∀ i ∈ S, 0 ≤ e i)
    (herror : ∀ i ∈ S, |f i - 1| ≤ e i) (hsmall : (∑ i ∈ S, e i) ≤ 1 / 2) :
    |(∏ i ∈ S, f i) - 1| ≤ 2 * ∑ i ∈ S, e i := by
  have hs := Finset.sum_nonneg he
  have he1 (i) (hi : i ∈ S) : e i ≤ 1 :=
    (Finset.single_le_sum he hi).trans (hsmall.trans (by norm_num))
  have hlo := one_sub_sum_le_positive_prod S f e hf (fun i hi => ⟨he i hi, he1 i hi⟩)
    (fun i hi => by have h := (abs_le.mp (herror i hi)).1; linarith)
  have hhi : (∏ i ∈ S, f i) ≤ 1 + 2 * ∑ i ∈ S, e i := by
    apply (Finset.prod_le_prod₀ hf (fun index hindex => ?_)).trans
      (prod_one_add_le_one_add_twice_sum S e he hsmall)
    have hupper := (abs_le.mp (herror index hindex)).2
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3

theorem reciprocal_square_le_reciprocal_difference {n : ℕ} (hn : 0 < n) :
    1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < (n : ℝ) + 1 := by positivity
  calc
    _ ≤ 1 / ((n : ℝ) * ((n : ℝ) + 1)) :=
      one_div_le_one_div_of_le (mul_pos hnR hp) (by nlinarith)
    _ = _ := by field_simp; ring

theorem finite_shifted_reciprocal_square_tail (S : Finset ℕ) {N : ℕ} (hN : 0 < N)
    (hS : ∀ n ∈ S, N ≤ n) :
    (∑ n ∈ S, 1 / ((n : ℝ) + 1) ^ 2) ≤ 1 / (N : ℝ) := by
  let B := max N (S.sup id + 1)
  have hNB : N ≤ B := Nat.le_max_left _ _
  have hsub : S ⊆ Finset.Ico N B := by
    intro n hn
    apply Finset.mem_Ico.mpr
    exact ⟨hS n hn, (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)).trans_le (Nat.le_max_right _ _)⟩
  have htel : (∑ n ∈ Finset.Ico N B, (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) =
      1 / (N : ℝ) - 1 / (B : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one, neg_sub_neg] using
      Finset.sum_Ico_sub (fun n : ℕ => -(1 / (n : ℝ))) hNB
  calc
    _ ≤ ∑ n ∈ Finset.Ico N B, 1 / ((n : ℝ) + 1) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ n ∈ Finset.Ico N B, (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact reciprocal_square_le_reciprocal_difference (hN.trans_le (Finset.mem_Ico.mp hn).1)
    _ = 1 / (N : ℝ) - 1 / (B : ℝ) := htel
    _ ≤ 1 / (N : ℝ) := sub_le_self _ (by positivity)

theorem finite_reciprocal_square_tail (S : Finset ℕ) {N : ℕ} (hN : 0 < N)
    (hS : ∀ n ∈ S, N < n) :
    (∑ n ∈ S, 1 / (n : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  have hinj : Set.InjOn (fun n : ℕ => n - 1) S := by
    intro n hn m hm h
    change n - 1 = m - 1 at h
    have hn' := hS n hn
    have hm' := hS m hm
    omega
  have hshift : (∑ n ∈ S.image (fun n : ℕ => (n - 1 : ℕ)), 1 / ((n : ℝ) + 1) ^ 2) =
      ∑ n ∈ S, 1 / (n : ℝ) ^ 2 := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    have heq : n - 1 + 1 = n := by have h := hS n hn; omega
    have hr : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast heq
    rw [hr]
  rw [← hshift]
  apply finite_shifted_reciprocal_square_tail _ hN
  intro n hn
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
  have h := hS m hm
  omega

theorem finite_positive_product_tail (S : Finset ℕ) (f : ℕ → ℝ) {N : ℕ} {K : ℝ}
    (hN : 0 < N) (hK : 0 ≤ K) (hS : ∀ n ∈ S, N < n)
    (hf : ∀ n ∈ S, 0 ≤ f n) (herror : ∀ n ∈ S, |f n - 1| ≤ K / (n : ℝ) ^ 2)
    (hsmall : K / N ≤ 1 / 2) :
    |(∏ n ∈ S, f n) - 1| ≤ 2 * K / N := by
  have hsum : (∑ n ∈ S, K / (n : ℝ) ^ 2) ≤ K / N := by
    have h := mul_le_mul_of_nonneg_left (finite_reciprocal_square_tail S hN hS) hK
    simpa only [Finset.mul_sum, mul_one_div] using h
  have h := positive_prod_sub_one_le_twice_sum S f (fun n => K / (n : ℝ) ^ 2)
    hf (fun _ _ => by positivity) herror (hsum.trans hsmall)
  exact h.trans ((mul_le_mul_of_nonneg_left hsum (by norm_num)).trans_eq (by ring))

theorem exists_uniform_positive_product_cutoff {K δ : ℝ} (hK : 0 ≤ K)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ N : ℕ, 0 < N ∧ ∀ (S : Finset ℕ) (f : ℕ → ℝ),
      (∀ n ∈ S, N < n) → (∀ n ∈ S, 0 ≤ f n) →
      (∀ n ∈ S, |f n - 1| ≤ K / (n : ℝ) ^ 2) → |(∏ n ∈ S, f n) - 1| ≤ δ := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 (2 * K / δ))
  have hN1 : (1 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hNpos : 0 < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN1)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hbound : 2 * K / N ≤ δ := by
    apply (div_le_iff₀ hNreal).mpr
    have h := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans hN)
    simpa only [mul_comm] using h
  refine ⟨N, hNpos, fun S f hS hf he => ?_⟩
  have hsmall : K / N ≤ 1 / 2 := by
    have h : 2 * (K / N) ≤ 1 := by
      simpa only [mul_div_assoc] using hbound.trans hδ1
    linarith
  exact (finite_positive_product_tail S f hNpos hK hS hf he hsmall).trans hbound

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_reciprocal_power_tail (S : Finset ℕ) {N k : ℕ} (hN : 0 < N)
    (hk : 2 ≤ k) (hS : ∀ n ∈ S, N < n) :
    (∑ n ∈ S, 1 / (n : ℝ) ^ k) ≤ 1 / (N : ℝ) ^ (k - 1) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsplit : k = 2 + (k - 2) := by omega
  have hsplit' : k - 1 = 1 + (k - 2) := by omega
  calc
    _ ≤ ∑ n ∈ S, (1 / (N : ℝ) ^ (k - 2)) * (1 / (n : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnR : (0 : ℝ) < n := hNR.trans (by exact_mod_cast hS n hn)
      have hp : (N : ℝ) ^ (k - 2) ≤ (n : ℝ) ^ (k - 2) :=
        pow_le_pow_left₀ hNR.le (by exact_mod_cast (hS n hn).le) _
      have hi := one_div_le_one_div_of_le (pow_pos hNR _) hp
      calc
        _ = (1 / (n : ℝ) ^ (k - 2)) * (1 / (n : ℝ) ^ 2) := by
          nth_rw 1 [hsplit]
          rw [pow_add]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hi (by positivity)
    _ = (1 / (N : ℝ) ^ (k - 2)) * ∑ n ∈ S, 1 / (n : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (1 / (N : ℝ) ^ (k - 2)) * (1 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (finite_reciprocal_square_tail S hN hS) (by positivity)
    _ = _ := by rw [hsplit', pow_add, pow_one]; ring

theorem finite_divisor_error_tail (S : Finset ℕ) {N k : ℕ} (hN : 0 < N)
    (hk : 2 ≤ k) (hS : ∀ n ∈ S, N < n) {L : ℝ} (hL : 0 < L) :
    (∑ n ∈ S, (1 / (n : ℝ) + 1 / L) ^ k) ≤
      2 ^ (k - 1) * (1 / (N : ℝ) ^ (k - 1) + (S.card : ℝ) / L ^ k) := by
  calc
    _ ≤ ∑ n ∈ S, (2 : ℝ) ^ (k - 1) * (1 / (n : ℝ) ^ k + 1 / L ^ k) := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [one_div_pow] using
        (add_pow_le (by positivity : 0 ≤ 1 / (n : ℝ)) (by positivity : 0 ≤ 1 / L) k)
    _ = 2 ^ (k - 1) * ((∑ n ∈ S, 1 / (n : ℝ) ^ k) + (S.card : ℝ) / L ^ k) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (finite_reciprocal_power_tail S hN hk hS) le_rfl) (by positivity)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

private theorem reciprocal_tenth_le_difference {n : ℕ} (hn : 0 < n) :
    1 / ((n : ℝ) + 1) ^ 10 ≤ 1 / (9 * (n : ℝ) ^ 9) - 1 / (9 * ((n : ℝ) + 1) ^ 9) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  apply (le_sub_iff_add_le).mpr
  have heq : 1 / ((n : ℝ) + 1) ^ 10 + 1 / (9 * ((n : ℝ) + 1) ^ 9) =
      ((n : ℝ) + 10) / (9 * ((n : ℝ) + 1) ^ 10) := by
    field_simp
    ring
  rw [heq]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hpoly : 0 ≤ ((n : ℝ) + 1) ^ 10 - ((n : ℝ) + 10) * (n : ℝ) ^ 9 := by
    ring_nf
    positivity
  nlinarith only [hpoly]

theorem finite_reciprocal_tenth_tail (S : Finset ℕ) {R : ℕ} (hR : 0 < R)
    (hS : ∀ d ∈ S, R < d) :
    (∑ d ∈ S, 1 / (d : ℝ) ^ 10) ≤ 1 / (9 * (R : ℝ) ^ 9) := by
  let shifted := S.image (fun d => d - 1)
  let B := max R (shifted.sup id + 1)
  have hRB : R ≤ B := Nat.le_max_left _ _
  have hshift : (∑ n ∈ shifted, 1 / ((n : ℝ) + 1) ^ 10) =
      ∑ d ∈ S, 1 / (d : ℝ) ^ 10 := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro d hd
      have heq : d - 1 + 1 = d := by have := hS d hd; omega
      have hreal : ((d - 1 : ℕ) : ℝ) + 1 = d := by exact_mod_cast heq
      rw [hreal]
    · intro d hd e he hde
      change d - 1 = e - 1 at hde
      have := hS d hd
      have := hS e he
      omega
  have hsub : shifted ⊆ Finset.Ico R B := by
    intro n hn
    obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp hn
    have hlo : R ≤ n := by have := hS d hd; omega
    exact Finset.mem_Ico.mpr ⟨hlo,
      (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)).trans_le (Nat.le_max_right _ _)⟩
  have htel : (∑ n ∈ Finset.Ico R B,
      (1 / (9 * (n : ℝ) ^ 9) - 1 / (9 * ((n : ℝ) + 1) ^ 9))) =
      1 / (9 * (R : ℝ) ^ 9) - 1 / (9 * (B : ℝ) ^ 9) := by
    convert Finset.sum_Ico_sub (fun n : ℕ => -(1 / (9 * (n : ℝ) ^ 9))) hRB using 1
    · apply Finset.sum_congr rfl
      intro n _
      push_cast
      ring
    · ring
  rw [← hshift]
  calc
    _ ≤ ∑ n ∈ Finset.Ico R B, 1 / ((n : ℝ) + 1) ^ 10 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ n ∈ Finset.Ico R B,
        (1 / (9 * (n : ℝ) ^ 9) - 1 / (9 * ((n : ℝ) + 1) ^ 9)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact reciprocal_tenth_le_difference (hR.trans_le (Finset.mem_Ico.mp hn).1)
    _ = _ := htel
    _ ≤ _ := sub_le_self _ (by positivity)

end Erdos3

end

end OAI
