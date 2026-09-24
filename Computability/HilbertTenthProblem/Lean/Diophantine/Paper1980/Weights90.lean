import Diophantine.Paper1980.Digits93

/-!
# Monomial weights of the 90-operation layout (base seven)

`Papers/1980/BINARY_PRODUCT_90_PROOF.md`, Section 3 (from
`PRODUCT_BOUND_91_PROOF.md`, Section 3): the physical coordinate `i` has the
weight `vᵢ = 8·7ⁱ`; a monomial is the multiset of its physical factors (the
input `x` has weight zero), with weight the sum of its factors' weights.  Sums
of at most six weights have base-seven digits below seven after division by
eight, so the weight of a monomial of degree at most six determines the
multiset of its factors (`W_inj`).
-/

namespace Jones1980

namespace L90

open Finset

/-- The weight of the physical coordinate `i`. -/
def v (i : ℕ) : ℕ := 8 * 7 ^ i

theorem v_pos (i : ℕ) : 0 < v i := by unfold v; positivity

theorem eight_dvd_v (i : ℕ) : 8 ∣ v i := ⟨7 ^ i, rfl⟩

theorem eight_le_v (i : ℕ) : 8 ≤ v i := by
  unfold v; have := Nat.one_le_pow i 7 (by norm_num); omega

theorem v_strictMono : StrictMono v := by
  intro i j hij
  unfold v
  exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by norm_num) hij) (by norm_num)

theorem v_inj {i k : ℕ} (h : v i = v k) : i = k := v_strictMono.injective h

/-- The bound `M = 8·7^(m−1)` on the weights of `m` coordinates. -/
def M (m : ℕ) : ℕ := 8 * 7 ^ (m - 1)

theorem M_pos (m : ℕ) : 0 < M m := by unfold M; positivity

theorem eight_le_M (m : ℕ) : 8 ≤ M m := by
  unfold M; have := Nat.one_le_pow (m - 1) 7 (by norm_num); omega

theorem eight_dvd_M (m : ℕ) : 8 ∣ M m := ⟨7 ^ (m - 1), rfl⟩

theorem v_le_M {m i : ℕ} (hi : i < m) : v i ≤ M m := by
  unfold v M; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))

variable {m : ℕ}

/-- The weight of a monomial: the sum of the weights of its physical factors. -/
def W (μ : Multiset (Fin m)) : ℕ := (μ.map fun i : Fin m => v (i : ℕ)).sum

@[simp] theorem W_zero : W (0 : Multiset (Fin m)) = 0 := by simp [W]

theorem W_add (μ ν : Multiset (Fin m)) : W (μ + ν) = W μ + W ν := by
  simp [W, Multiset.map_add, Multiset.sum_add]

@[simp] theorem W_singleton (i : Fin m) : W ({i} : Multiset (Fin m)) = v i := by simp [W]

theorem W_cons (i : Fin m) (μ : Multiset (Fin m)) : W (i ::ₘ μ) = v i + W μ := by
  simp [W, Multiset.map_cons, Multiset.sum_cons]

theorem W_pair (i k : Fin m) : W ({i, k} : Multiset (Fin m)) = v i + v k := by
  simp [W]

theorem eight_dvd_W (μ : Multiset (Fin m)) : 8 ∣ W μ := by
  unfold W
  exact Multiset.dvd_sum (fun x hx => by
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.1 hx
    exact eight_dvd_v i)

theorem W_le (μ : Multiset (Fin m)) : W μ ≤ Multiset.card μ * M m := by
  unfold W
  induction μ using Multiset.induction_on with
  | empty => simp
  | cons i μ ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, add_mul, one_mul]
    have := v_le_M (m := m) i.isLt
    omega

theorem W_pos_of_ne_zero {μ : Multiset (Fin m)} (hμ : μ ≠ 0) : 8 ≤ W μ := by
  obtain ⟨i, hi⟩ := Multiset.exists_mem_of_ne_zero hμ
  obtain ⟨ν, rfl⟩ := Multiset.exists_cons_of_mem hi
  rw [W_cons]; have := eight_le_v i; omega

theorem W_eq_sum_count (μ : Multiset (Fin m)) :
    W μ = 8 * ∑ i : Fin m, μ.count i * 7 ^ (i : ℕ) := by
  unfold W
  rw [Finset.sum_multiset_map_count, Finset.mul_sum]
  have : ∑ i ∈ μ.toFinset, μ.count i • v i = ∑ i : Fin m, μ.count i • v i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    rw [Multiset.mem_toFinset] at hi
    rw [Multiset.count_eq_zero.2 hi, zero_smul]
  rw [this]
  apply Finset.sum_congr rfl
  intro i _
  simp only [v, smul_eq_mul]; ring

/-- The count of a factor is a base-seven digit of `W/8` when the degree is at most six. -/
theorem count_eq_digit (μ : Multiset (Fin m)) (hμ : Multiset.card μ ≤ 6) (i : Fin m) :
    μ.count i = (W μ / 8) / 7 ^ (i : ℕ) % 7 := by
  rw [W_eq_sum_count, Nat.mul_div_cancel_left _ (by norm_num)]
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ, c = fun j => if h : j < m then μ.count ⟨j, h⟩ else 0 :=
    ⟨_, rfl⟩
  have hsum : ∑ j : Fin m, μ.count j * 7 ^ (j : ℕ) = ∑ j ∈ range m, c j * 7 ^ j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => c j * 7 ^ j) m]
    apply Finset.sum_congr rfl
    intro j _
    rw [hc]; simp only [j.isLt, dif_pos, Fin.eta]
  have hlt : ∀ j, c j < 7 := by
    intro j; rw [hc]; dsimp only
    split_ifs
    · exact lt_of_le_of_lt (le_trans (Multiset.count_le_card _ _) hμ) (by norm_num)
    · norm_num
  rw [hsum, Iso.digit_sum (B := 7) (by norm_num) (i : ℕ) c hlt m, if_pos i.isLt, hc]
  simp only [i.isLt, dif_pos, Fin.eta]

/-- Weight injectivity for monomials of degree at most six. -/
theorem W_inj {μ ν : Multiset (Fin m)} (hμ : Multiset.card μ ≤ 6) (hν : Multiset.card ν ≤ 6)
    (h : W μ = W ν) : μ = ν := by
  apply Multiset.ext'
  intro i
  rw [count_eq_digit μ hμ i, count_eq_digit ν hν i, h]

/-- Weights of monomials of degree at most two: `0`, `vᵢ`, `vᵢ + v_k`. -/
theorem W_card_le_two (μ : Multiset (Fin m)) (hμ : Multiset.card μ ≤ 2) :
    μ = 0 ∨ (∃ i, μ = {i}) ∨ ∃ i k, μ = {i, k} := by
  rcases Nat.lt_or_ge (Multiset.card μ) 1 with h | h
  · left; exact Multiset.card_eq_zero.1 (by omega)
  rcases Nat.lt_or_ge (Multiset.card μ) 2 with h2 | h2
  · right; left; exact Multiset.card_eq_one.1 (by omega)
  · right; right; exact Multiset.card_eq_two.1 (by omega)

end L90

end Jones1980
