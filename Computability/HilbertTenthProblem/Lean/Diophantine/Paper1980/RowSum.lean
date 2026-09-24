import Diophantine.Paper1980.TagRows

/-!
# Words built from a row function

For the converse direction of the alternative systems the packed words are assembled from
their rows: `rowsum f m t = Σ_{i<t} f i · 3^(m i)`.  This file proves the three facts that
make such a word usable: it is below `3^(m t)`, its rows below `t` are the values of `f`,
and it is Boolean as soon as every row is (all under the standing assumption that each row
is below `3^m`).
-/

namespace Jones1980

namespace Ternary

open Finset

/-- A Boolean chunk below `3^e` followed by a Boolean word is Boolean. -/
theorem bool3_chunk_cons {X Y e : ℕ} (hX : Bool3 X) (hXlt : X < 3 ^ e) (hY : Bool3 Y) :
    Bool3 (X + 3 ^ e * Y) := by
  intro p
  rcases Nat.lt_or_ge p e with hp | hp
  · rw [mul_comm, dg_add_mul_pow hp]; exact hX p
  · obtain ⟨p', rfl⟩ := Nat.exists_eq_add_of_le hp
    have e1 : dg (X + 3 ^ e * Y) (e + p') = dg Y p' := by
      unfold dg
      rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt hXlt, zero_add]
    rw [e1]; exact hY p'

theorem chunk_cons_lt {X Y e k : ℕ} (hXlt : X < 3 ^ e) (hY : Y < 3 ^ (k * e)) :
    X + 3 ^ e * Y < 3 ^ ((k + 1) * e) := by
  have h1 : Y + 1 ≤ 3 ^ (k * e) := hY
  have h2 : 3 ^ e * (Y + 1) ≤ 3 ^ e * 3 ^ (k * e) := Nat.mul_le_mul_left _ h1
  rw [← pow_add] at h2
  have e1 : e + k * e = (k + 1) * e := by ring
  rw [e1] at h2
  nlinarith

/-- The word with rows `f 0, f 1, …, f (t−1)` at the radix `R = 3^m`. -/
def rowsum (f : ℕ → ℕ) (m t : ℕ) : ℕ := ∑ i ∈ range t, f i * 3 ^ (m * i)

theorem rowsum_zero (f : ℕ → ℕ) (m : ℕ) : rowsum f m 0 = 0 := by simp [rowsum]

theorem rowsum_succ (f : ℕ → ℕ) (m t : ℕ) :
    rowsum f m (t + 1) = rowsum f m t + f t * 3 ^ (m * t) := by
  simp [rowsum, sum_range_succ]

/-- Peeling the lowest row. -/
theorem rowsum_succ' (f : ℕ → ℕ) (m t : ℕ) :
    rowsum f m (t + 1) = f 0 + 3 ^ m * rowsum (fun i => f (i + 1)) m t := by
  unfold rowsum
  rw [sum_range_succ']
  simp only [mul_zero, pow_zero, mul_one]
  rw [add_comm]
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [show m * (i + 1) = m + m * i by ring, pow_add]
  ring

theorem rowsum_lt {f : ℕ → ℕ} {m : ℕ} (hlt : ∀ i, f i < 3 ^ m) : ∀ t, rowsum f m t < 3 ^ (m * t)
  | 0 => by simp [rowsum_zero]
  | t + 1 => by
    rw [rowsum_succ' f m t]
    have ih := rowsum_lt (f := fun i => f (i + 1)) (fun i => hlt (i + 1)) t
    have h1 : rowsum (fun i => f (i + 1)) m t + 1 ≤ 3 ^ (m * t) := ih
    have h2 : 3 ^ m * (rowsum (fun i => f (i + 1)) m t + 1) ≤ 3 ^ m * 3 ^ (m * t) :=
      Nat.mul_le_mul_left _ h1
    rw [← pow_add] at h2
    have e : m + m * t = m * (t + 1) := by ring
    rw [e, Nat.mul_add, mul_one] at h2
    have := hlt 0
    omega

theorem row_rowsum {f : ℕ → ℕ} {m : ℕ} (hlt : ∀ i, f i < 3 ^ m) :
    ∀ t i, i < t → row (rowsum f m t) m i = f i
  | 0, i, hi => by omega
  | t + 1, 0, _ => by
    rw [rowsum_succ' f m t]
    unfold row
    rw [mul_zero, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hlt 0)]
  | t + 1, i + 1, hi => by
    rw [rowsum_succ' f m t]
    have ih := row_rowsum (f := fun i => f (i + 1)) (fun i => hlt (i + 1)) t i (by omega)
    unfold row at ih ⊢
    rw [show m * (i + 1) = m + m * i by ring, pow_add, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (hlt 0), zero_add]
    exact ih

theorem bool3_rowsum {f : ℕ → ℕ} {m : ℕ} (hb : ∀ i, Bool3 (f i)) (hlt : ∀ i, f i < 3 ^ m) :
    ∀ t, Bool3 (rowsum f m t)
  | 0 => by rw [rowsum_zero]; exact bool3_zero
  | t + 1 => by
    rw [rowsum_succ' f m t]
    exact bool3_chunk_cons (hb 0) (hlt 0)
      (bool3_rowsum (f := fun i => f (i + 1)) (fun i => hb (i + 1)) (fun i => hlt (i + 1)) t)

/-- A row-sum whose rows are pointwise below another's is below it. -/
theorem rowsum_le {f g : ℕ → ℕ} {m : ℕ} (h : ∀ i, f i ≤ g i) (t : ℕ) :
    rowsum f m t ≤ rowsum g m t :=
  sum_le_sum fun i _ => Nat.mul_le_mul_right _ (h i)

theorem rowsum_add (f g : ℕ → ℕ) (m t : ℕ) :
    rowsum (fun i => f i + g i) m t = rowsum f m t + rowsum g m t := by
  unfold rowsum
  rw [← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

theorem rowsum_mul (c : ℕ) (f : ℕ → ℕ) (m t : ℕ) :
    rowsum (fun i => c * f i) m t = c * rowsum f m t := by
  unfold rowsum
  rw [mul_sum]
  exact sum_congr rfl fun i _ => by ring

theorem rowsum_sub {f g : ℕ → ℕ} (h : ∀ i, g i ≤ f i) (m t : ℕ) :
    rowsum (fun i => f i - g i) m t = rowsum f m t - rowsum g m t := by
  have hle := rowsum_le h t (m := m)
  have hadd : rowsum (fun i => f i - g i) m t + rowsum g m t = rowsum f m t := by
    rw [← rowsum_add]
    unfold rowsum
    exact sum_congr rfl fun i _ => by simp only [Nat.sub_add_cancel (h i)]
  omega

/-- `heads` as a row sum. -/
theorem heads_eq_rowsum (m t : ℕ) : heads m t = rowsum (fun _ => 1) m t := by
  unfold heads rowsum
  exact sum_congr rfl fun i _ => by ring

end Ternary

end Jones1980
