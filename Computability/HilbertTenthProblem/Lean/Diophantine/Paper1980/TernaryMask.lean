import Mathlib.Data.Nat.Multiplicity
import Mathlib.Order.Interval.Finset.Nat

/-!
# The unit-two ternary mask (Kummer's theorem for the prime three)

`Papers/1980/EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md`, §1.  For `N ≥ 1`, `L = 3^N` and
`P < L`,

    L ∣ C(2P, P)  ⟺  the lowest ternary digit of P is 2 and the digits at the
                     positions 1, …, N − 1 are nonzero.

Kummer's theorem (`Nat.emultiplicity_choose`) counts the carries when `P` is added to
itself in base three; there is a carry out of position `i − 1` exactly when
`3^i ≤ 2 (P mod 3^i)`.  With `P < 3^N` there are at most `N` positions, so the
valuation is `N` exactly when every one of the `N` positions carries; and the carry
conditions unfold digit by digit (`carry_step`): position `0` carries iff its digit is
`2`, and with an incoming carry a position carries iff its digit is nonzero.
-/

namespace Jones1980

namespace Ternary

open Finset

/-- With an incoming carry (`3^i ≤ 2 (P mod 3^i)`), position `i` carries iff its digit is
nonzero. -/
theorem carry_step {P i : ℕ} (hi : 3 ^ i ≤ 2 * (P % 3 ^ i)) :
    3 ^ (i + 1) ≤ 2 * (P % 3 ^ (i + 1)) ↔ (P / 3 ^ i) % 3 ≠ 0 := by
  rw [Nat.mod_pow_succ, pow_succ]
  have hm : P % 3 ^ i < 3 ^ i := Nat.mod_lt _ (by positivity)
  have hd : (P / 3 ^ i) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize P % 3 ^ i = m at *
  generalize (P / 3 ^ i) % 3 = d at *
  generalize 3 ^ i = t at *
  interval_cases d <;> omega

/-- The carry conditions at the positions `1, …, N` are equivalent to the digit conditions. -/
theorem carries_iff {N P : ℕ} (hN : 1 ≤ N) :
    (∀ i, 1 ≤ i → i ≤ N → 3 ^ i ≤ 2 * (P % 3 ^ i)) ↔
      (P % 3 = 2 ∧ ∀ i, 1 ≤ i → i < N → (P / 3 ^ i) % 3 ≠ 0) := by
  have h1 : 3 ^ 1 ≤ 2 * (P % 3 ^ 1) ↔ P % 3 = 2 := by
    rw [pow_one]; have := Nat.mod_lt P (show 0 < 3 by norm_num); omega
  constructor
  · intro hC
    refine ⟨h1.1 (hC 1 le_rfl hN), fun i hi hiN => ?_⟩
    exact (carry_step (hC i hi hiN.le)).1 (hC (i + 1) (by omega) (by omega))
  · rintro ⟨h0, hd⟩ i hi hiN
    induction i with
    | zero => omega
    | succ i ih =>
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; exact h1.2 h0
      · exact (carry_step (ih h (by omega))).2 (hd i h (by omega))

/-- The unit-two ternary mask: for `N ≥ 1` and `P < 3^N`, `3^N ∣ C(2P, P)` iff the lowest
ternary digit of `P` is `2` and the digits at the positions `1, …, N − 1` are nonzero. -/
theorem ternary_mask {N P : ℕ} (hN : 1 ≤ N) (hP : P < 3 ^ N) :
    3 ^ N ∣ (2 * P).choose P ↔
      (P % 3 = 2 ∧ ∀ i, 1 ≤ i → i < N → (P / 3 ^ i) % 3 ≠ 0) := by
  rw [← carries_iff hN]
  rcases Nat.eq_zero_or_pos P with h0 | h0
  · subst h0
    simp only [mul_zero, Nat.choose_self]
    constructor
    · intro h
      have h3 : 3 ≤ 3 ^ N := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ N := Nat.pow_le_pow_right (by norm_num) hN
      have := Nat.le_of_dvd one_pos h
      omega
    · intro h
      have := h 1 le_rfl hN
      simp at this
  have hlog : Nat.log 3 (2 * P) < N + 1 :=
    Nat.log_lt_of_lt_pow (by omega) (by rw [pow_succ]; omega)
  have hK := Nat.prime_three.emultiplicity_choose (show P ≤ 2 * P by omega) hlog
  rw [show 2 * P - P = P by omega] at hK
  rw [pow_dvd_iff_le_emultiplicity, hK, Nat.cast_le]
  constructor
  · intro hcard i hi hiN
    have heq : (Ico 1 (N + 1)).filter (fun i => 3 ^ i ≤ P % 3 ^ i + P % 3 ^ i) = Ico 1 (N + 1) :=
      eq_of_subset_of_card_le (filter_subset _ _) (by rw [Nat.card_Ico]; omega)
    have hmem : i ∈ (Ico 1 (N + 1)).filter (fun i => 3 ^ i ≤ P % 3 ^ i + P % 3 ^ i) := by
      rw [heq, mem_Ico]; omega
    rw [mem_filter] at hmem
    omega
  · intro hC
    have heq : (Ico 1 (N + 1)).filter (fun i => 3 ^ i ≤ P % 3 ^ i + P % 3 ^ i) = Ico 1 (N + 1) := by
      apply filter_true_of_mem
      intro i hi
      rw [mem_Ico] at hi
      have := hC i hi.1 (by omega)
      omega
    rw [heq, Nat.card_Ico]; omega

/-! ### Subtracting the repunit

`2r + 1 = D₀ + P` with `D₀ = 3^N` and `r` a mask word (unit digit `2`, other digits
nonzero) gives `P = 2(r − rep N)` where `rep N = (3^N − 1)/2 = 1…1` (N ones); the
subtraction has no borrow, so `r − rep N` is a Boolean ternary word with unit digit `1`
(`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §2). -/

/-- The base-three repunit `Σ_{i<N} 3^i = (3^N − 1)/2`. -/
def rep : ℕ → ℕ
  | 0 => 0
  | N + 1 => rep N + 3 ^ N

theorem rep_zero : rep 0 = 0 := rfl
theorem rep_succ (N : ℕ) : rep (N + 1) = rep N + 3 ^ N := rfl

theorem two_mul_rep_add_one : ∀ N, 2 * rep N + 1 = 3 ^ N
  | 0 => rfl
  | N + 1 => by rw [rep_succ, pow_succ]; have := two_mul_rep_add_one N; omega

theorem rep_lt (N : ℕ) : rep N < 3 ^ N := by have := two_mul_rep_add_one N; omega

theorem rep_add (m : ℕ) : ∀ n, rep (m + n) = rep m + 3 ^ m * rep n
  | 0 => by simp [rep_zero]
  | n + 1 => by
    rw [← add_assoc, rep_succ, rep_add m n, rep_succ, pow_add]; ring

theorem rep_mod {i N : ℕ} (h : i ≤ N) : rep N % 3 ^ i = rep i := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [rep_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (rep_lt i)]

/-- The low parts of a mask word dominate the repunits. -/
theorem rep_le_mod {N r : ℕ} (h0 : r % 3 = 2) (hd : ∀ i, 1 ≤ i → i < N → r / 3 ^ i % 3 ≠ 0) :
    ∀ i, i ≤ N → rep i ≤ r % 3 ^ i := by
  intro i
  induction i with
  | zero => intro _; simp [rep_zero]
  | succ i ih =>
    intro hi
    rw [Nat.mod_pow_succ, rep_succ]
    have h1 : 1 ≤ r / 3 ^ i % 3 := by
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; simp [h0]
      · have := hd i h (by omega); omega
    have h2 := ih (by omega)
    have h3 : 3 ^ i * 1 ≤ 3 ^ i * (r / 3 ^ i % 3) := Nat.mul_le_mul_left _ h1
    omega

/-- Subtracting the repunit from a mask word: no borrow, digitwise. -/
theorem sub_rep_mod {N r : ℕ} (hr : r < 3 ^ N) (h0 : r % 3 = 2)
    (hd : ∀ i, 1 ≤ i → i < N → r / 3 ^ i % 3 ≠ 0) :
    rep N ≤ r ∧ ∀ i, i ≤ N → r % 3 ^ i = (r - rep N) % 3 ^ i + rep i := by
  have hle : rep N ≤ r := by
    have := rep_le_mod h0 hd N le_rfl
    rw [Nat.mod_eq_of_lt hr] at this
    exact this
  refine ⟨hle, ?_⟩
  obtain ⟨P, hP⟩ : ∃ P, P = r - rep N := ⟨_, rfl⟩
  have hrP : r = P + rep N := by omega
  rw [← hP]
  intro i
  induction i with
  | zero => intro _; simp [rep_zero, Nat.mod_one]
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    -- `r mod 3^(i+1) = (P mod 3^(i+1) + rep (i+1)) mod 3^(i+1)`
    have hmod : r % 3 ^ (i + 1) = (P % 3 ^ (i + 1) + rep (i + 1)) % 3 ^ (i + 1) := by
      rw [hrP, Nat.add_mod, rep_mod hi]
    rw [Nat.mod_pow_succ] at hmod ⊢
    rw [Nat.mod_pow_succ (x := P), rep_succ] at hmod ⊢
    have ha : r / 3 ^ i % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have ha1 : 1 ≤ r / 3 ^ i % 3 := by
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; simp [h0]
      · have := hd i h (by omega); omega
    have hb : P / 3 ^ i % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hp : P % 3 ^ i < 3 ^ i := Nat.mod_lt _ (by positivity)
    have hm : r % 3 ^ i < 3 ^ i := Nat.mod_lt _ (by positivity)
    have hrep : rep i < 3 ^ i := rep_lt i
    rw [pow_succ] at hmod
    rw [ih'] at hmod ⊢
    generalize r / 3 ^ i % 3 = A at *
    generalize P / 3 ^ i % 3 = B at *
    generalize P % 3 ^ i = p at *
    generalize rep i = e at *
    generalize 3 ^ i = T at *
    interval_cases A <;> interval_cases B <;>
      first
      | (rw [Nat.mod_eq_of_lt (by omega)] at hmod; omega)
      | (rw [show p + T * 2 + (e + T) = p + e + T * 3 by ring, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)] at hmod; omega)

/-- `r − rep N` is a Boolean ternary word with unit digit `1`. -/
theorem sub_rep {N r : ℕ} (hN : 1 ≤ N) (hr : r < 3 ^ N) (h0 : r % 3 = 2)
    (hd : ∀ i, 1 ≤ i → i < N → r / 3 ^ i % 3 ≠ 0) :
    rep N ≤ r ∧ (r - rep N) % 3 = 1 ∧ ∀ i, (r - rep N) / 3 ^ i % 3 ≤ 1 := by
  obtain ⟨hle, hmod⟩ := sub_rep_mod hr h0 hd
  -- the digits below `N`: `d_i(r) = d_i(P) + 1`
  have hdig : ∀ i, i < N → (r - rep N) / 3 ^ i % 3 + 1 = r / 3 ^ i % 3 := by
    intro i hi
    have h1 := hmod i hi.le
    have h2 := hmod (i + 1) hi
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ (x := r - rep N), rep_succ, h1] at h2
    have h3 : 3 ^ i * (r / 3 ^ i % 3) = 3 ^ i * ((r - rep N) / 3 ^ i % 3 + 1) := by
      rw [mul_add, mul_one]; omega
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) h3).symm
  refine ⟨hle, ?_, ?_⟩
  · have := hdig 0 hN
    simp only [pow_zero, Nat.div_one] at this
    omega
  · intro i
    rcases Nat.lt_or_ge i N with hi | hi
    · have h1 := hdig i hi
      have h2 : r / 3 ^ i % 3 < 3 := Nat.mod_lt _ (by norm_num)
      omega
    · have h3 : r - rep N < 3 ^ i := by
        calc r - rep N ≤ r := Nat.sub_le _ _
          _ < 3 ^ N := hr
          _ ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) hi
      rw [Nat.div_eq_of_lt h3]; simp

end Ternary

end Jones1980
