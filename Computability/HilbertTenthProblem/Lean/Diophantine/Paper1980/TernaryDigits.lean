import Diophantine.Paper1980.TernaryMask
import Mathlib.Tactic

/-!
# Ternary digits: extraction, carry-free sums, the carry recurrence, Boolean words

Shared toolkit for the decoding of the alternative universal systems (the
counter-machine and tag-system routes of `Papers/1980/EXPLORATION_*.md`), whose
packed words are Boolean ternary numbers read in rows and base-`q` chunks.

* `dg X p = X / 3^p % 3` is the ternary digit of `X` at position `p`; `val c n =
  Σ_{p<n} c p · 3^p` is the number with digit coefficients `c`.  When all
  coefficients are at most `2` the digits of `val c n` are the coefficients
  (`dg_val`), and every `X < 3^n` is `val (dg X) n` (`val_dg`).  Hence a sum of
  words whose digitwise sum never exceeds `2` has no carries (`dg_add_of_le_two`).
* The carry recurrence for `αX + βY`: with `carry α β X Y p = (α(X mod 3^p) +
  β(Y mod 3^p)) / 3^p`, `dg (αX + βY) p = (α dg X p + β dg Y p + carry p) mod 3` and
  `carry (p+1) = (α dg X p + β dg Y p + carry p) / 3` (`dg_lin`, `carry_succ`).
* `Bool3 X` (all digits at most `1`): closure under shifts, chunks and disjoint sums,
  `X ≤ rep n` for `X < 3^n`, and the disjointness of two Boolean summands of a
  Boolean sum (`bool3_add_disjoint`).
* Base-`q` chunks `q = 3^e`: a Boolean word's chunk is Boolean and at most
  `rep e = (q − 1)/2`; the signed-field decoding step `chunk_step`: if
  `P = f + q P'` with `−q/2 < f < q` then `f = P mod q` and `P' = P / q`.
-/

namespace Jones1980

namespace Ternary

open Finset

/-! ### Digits -/

/-- The ternary digit of `X` at position `p`. -/
def dg (X p : ℕ) : ℕ := X / 3 ^ p % 3

theorem dg_lt (X p : ℕ) : dg X p < 3 := Nat.mod_lt _ (by norm_num)

theorem dg_le_two (X p : ℕ) : dg X p ≤ 2 := by have := dg_lt X p; omega

@[simp] theorem dg_zero (p : ℕ) : dg 0 p = 0 := by simp [dg]

theorem dg_zero_pos (X : ℕ) : dg X 0 = X % 3 := by simp [dg]

theorem dg_eq_zero_of_lt {X p : ℕ} (h : X < 3 ^ p) : dg X p = 0 := by
  simp [dg, Nat.div_eq_of_lt h]

theorem mod_pow_succ_dg (X p : ℕ) : X % 3 ^ (p + 1) = X % 3 ^ p + 3 ^ p * dg X p :=
  Nat.mod_pow_succ

theorem dg_div_pow (X s p : ℕ) : dg (X / 3 ^ s) p = dg X (s + p) := by
  simp [dg, Nat.div_div_eq_div_mul, pow_add]

theorem dg_mul_pow_add (X s p : ℕ) : dg (3 ^ s * X) (s + p) = dg X p := by
  have h3 : 0 < 3 ^ s := by positivity
  simp only [dg, pow_add]
  rw [Nat.mul_div_mul_left _ _ h3]

theorem dg_mul_pow_of_lt {s p : ℕ} (X : ℕ) (h : p < s) : dg (3 ^ s * X) p = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, s = p + (k + 1) := ⟨s - p - 1, by omega⟩
  have e : 3 ^ (p + (k + 1)) * X = 3 ^ p * (3 * (3 ^ k * X)) := by ring
  unfold dg
  rw [e, Nat.mul_div_cancel_left _ (by positivity)]
  simp

theorem dg_mod_pow_of_lt {s p : ℕ} (X : ℕ) (h : p < s) : dg (X % 3 ^ s) p = dg X p := by
  obtain ⟨k, rfl⟩ : ∃ k, s = p + (k + 1) := ⟨s - p - 1, by omega⟩
  unfold dg
  rw [pow_add, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (by omega))]

theorem dg_mod_pow_of_ge {s p : ℕ} (X : ℕ) (h : s ≤ p) : dg (X % 3 ^ s) p = 0 :=
  dg_eq_zero_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
    (Nat.pow_le_pow_right (by norm_num) h))

theorem dg_pow (k p : ℕ) : dg (3 ^ k) p = if p = k then 1 else 0 := by
  split_ifs with h
  · subst h; simp [dg, Nat.div_self (show 0 < 3 ^ p by positivity)]
  · rcases Nat.lt_or_gt_of_ne h with hlt | hgt
    · rw [← mul_one (3 ^ k), dg_mul_pow_of_lt _ hlt]
    · exact dg_eq_zero_of_lt (Nat.pow_lt_pow_right (by norm_num) hgt)

theorem dg_add_mul_pow {X Y k p : ℕ} (h : p < k) : dg (X + Y * 3 ^ k) p = dg X p := by
  obtain ⟨j, rfl⟩ : ∃ j, k = p + (j + 1) := ⟨k - p - 1, by omega⟩
  simp only [dg]
  rw [show Y * 3 ^ (p + (j + 1)) = 3 ^ p * (3 * (Y * 3 ^ j)) by ring,
    Nat.add_mul_div_left _ _ (by positivity)]
  simp

/-! ### Coefficient sums -/

/-- The number with digit coefficients `c` at the positions below `n`. -/
def val (c : ℕ → ℕ) (n : ℕ) : ℕ := ∑ p ∈ range n, c p * 3 ^ p

theorem val_zero (c : ℕ → ℕ) : val c 0 = 0 := by simp [val]

theorem val_succ (c : ℕ → ℕ) (n : ℕ) : val c (n + 1) = val c n + c n * 3 ^ n := by
  simp [val, sum_range_succ]

theorem val_lt {c : ℕ → ℕ} (hc : ∀ p, c p ≤ 2) : ∀ n, val c n < 3 ^ n
  | 0 => by simp [val_zero]
  | n + 1 => by
    rw [val_succ, pow_succ]
    have h1 := val_lt hc n
    have h2 : c n * 3 ^ n ≤ 2 * 3 ^ n := Nat.mul_le_mul_right _ (hc n)
    omega

theorem val_dg_eq_mod (X : ℕ) : ∀ n, val (dg X) n = X % 3 ^ n
  | 0 => by simp [val_zero, Nat.mod_one]
  | n + 1 => by rw [val_succ, val_dg_eq_mod X n, mod_pow_succ_dg]; ring

theorem val_dg {X n : ℕ} (h : X < 3 ^ n) : val (dg X) n = X := by
  rw [val_dg_eq_mod, Nat.mod_eq_of_lt h]

theorem val_add (c d : ℕ → ℕ) (n : ℕ) : val c n + val d n = val (fun p => c p + d p) n := by
  simp [val, ← sum_add_distrib, add_mul]

theorem dg_val {c : ℕ → ℕ} (hc : ∀ p, c p ≤ 2) {p n : ℕ} (h : p < n) : dg (val c n) p = c p := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [val_succ]
    rcases Nat.lt_or_ge p n with hpn | hpn
    · rw [dg_add_mul_pow hpn, ih hpn]
    · have hpn' : p = n := by omega
      subst hpn'
      have hv := val_lt hc p
      have hT : 0 < 3 ^ p := by positivity
      unfold dg
      rw [Nat.add_mul_div_right _ _ hT, Nat.div_eq_of_lt hv, zero_add,
        Nat.mod_eq_of_lt (by have := hc p; omega)]

theorem dg_val_of_ge {c : ℕ → ℕ} (hc : ∀ p, c p ≤ 2) {p n : ℕ} (h : n ≤ p) :
    dg (val c n) p = 0 :=
  dg_eq_zero_of_lt (lt_of_lt_of_le (val_lt hc n) (Nat.pow_le_pow_right (by norm_num : 0 < 3) h))

theorem lt_pow_self' (X : ℕ) : X < 3 ^ X := Nat.lt_pow_self (by norm_num)

/-- A sum whose digitwise sum never exceeds `2` has no carries. -/
theorem dg_add_of_le_two {X Y : ℕ} (h : ∀ p, dg X p + dg Y p ≤ 2) (p : ℕ) :
    dg (X + Y) p = dg X p + dg Y p := by
  have hn : ∀ m, m ≤ X + Y + p + 1 → m < 3 ^ (X + Y + p + 1) :=
    fun m hm => lt_of_le_of_lt hm (lt_pow_self' _)
  obtain ⟨n, hX, hY, hp⟩ : ∃ n, X < 3 ^ n ∧ Y < 3 ^ n ∧ p < n :=
    ⟨X + Y + p + 1, hn X (by omega), hn Y (by omega), by omega⟩
  have e : X + Y = val (fun p => dg X p + dg Y p) n := by
    rw [← val_add, val_dg hX, val_dg hY]
  rw [e, dg_val h hp]

/-- A three-term sum whose digitwise sum never exceeds `2` has no carries. -/
theorem dg_add3_of_le_two {X Y Z : ℕ} (h : ∀ p, dg X p + dg Y p + dg Z p ≤ 2) (p : ℕ) :
    dg (X + Y + Z) p = dg X p + dg Y p + dg Z p := by
  have h1 : ∀ p, dg X p + dg Y p ≤ 2 := fun p => by have := h p; omega
  have h2 : ∀ p, dg (X + Y) p + dg Z p ≤ 2 := fun p => by rw [dg_add_of_le_two h1]; exact h p
  rw [dg_add_of_le_two h2, dg_add_of_le_two h1]

/-! ### The carry recurrence -/

/-- The carry into position `p` of `αX + βY`. -/
def carry (α β X Y p : ℕ) : ℕ := (α * (X % 3 ^ p) + β * (Y % 3 ^ p)) / 3 ^ p

@[simp] theorem carry_zero (α β X Y : ℕ) : carry α β X Y 0 = 0 := by simp [carry, Nat.mod_one]

theorem lin_mod_pow (α β X Y p : ℕ) :
    (α * X + β * Y) % 3 ^ p = (α * (X % 3 ^ p) + β * (Y % 3 ^ p)) % 3 ^ p :=
  Nat.ModEq.add (Nat.ModEq.mul_left α (Nat.mod_modEq X _).symm)
    (Nat.ModEq.mul_left β (Nat.mod_modEq Y _).symm)

theorem lin_mod_pow_succ (α β X Y p : ℕ) :
    (α * X + β * Y) % 3 ^ (p + 1) =
      (α * X + β * Y) % 3 ^ p + 3 ^ p * ((α * dg X p + β * dg Y p + carry α β X Y p) % 3) ∧
    carry α β X Y (p + 1) = (α * dg X p + β * dg Y p + carry α β X Y p) / 3 := by
  have hT : 0 < 3 ^ p := by positivity
  have hX : X % 3 ^ (p + 1) = X % 3 ^ p + 3 ^ p * dg X p := mod_pow_succ_dg X p
  have hY : Y % 3 ^ (p + 1) = Y % 3 ^ p + 3 ^ p * dg Y p := mod_pow_succ_dg Y p
  have hρ : α * (X % 3 ^ p) + β * (Y % 3 ^ p) =
      3 ^ p * carry α β X Y p + (α * X + β * Y) % 3 ^ p := by
    rw [lin_mod_pow, carry]; exact (Nat.div_add_mod _ _).symm
  have hρlt : (α * X + β * Y) % 3 ^ p < 3 ^ p := Nat.mod_lt _ hT
  have hsum : α * (X % 3 ^ (p + 1)) + β * (Y % 3 ^ (p + 1)) =
      3 ^ p * (α * dg X p + β * dg Y p + carry α β X Y p) + (α * X + β * Y) % 3 ^ p := by
    rw [hX, hY]
    have : α * (X % 3 ^ p + 3 ^ p * dg X p) + β * (Y % 3 ^ p + 3 ^ p * dg Y p) =
        (α * (X % 3 ^ p) + β * (Y % 3 ^ p)) + 3 ^ p * (α * dg X p + β * dg Y p) := by ring
    rw [this, hρ]; ring
  have h3T : 3 ^ (p + 1) = 3 ^ p * 3 := pow_succ 3 p
  constructor
  · rw [lin_mod_pow _ _ _ _ (p + 1), hsum, h3T]
    obtain ⟨u, v, huv, hv⟩ : ∃ u v, α * dg X p + β * dg Y p + carry α β X Y p = 3 * u + v ∧
        v < 3 :=
      ⟨_ / 3, _ % 3, (Nat.div_add_mod _ 3).symm, Nat.mod_lt _ (by norm_num)⟩
    rw [huv]
    have e1 : 3 ^ p * (3 * u + v) + (α * X + β * Y) % 3 ^ p =
        (3 ^ p * v + (α * X + β * Y) % 3 ^ p) + u * (3 ^ p * 3) := by ring
    have hlt : 3 ^ p * v + (α * X + β * Y) % 3 ^ p < 3 ^ p * 3 := by
      have : 3 ^ p * v ≤ 3 ^ p * 2 := Nat.mul_le_mul_left _ (by omega)
      omega
    rw [e1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    have e2 : (3 * u + v) % 3 = v := by omega
    rw [e2]; ring
  · rw [carry, hsum, h3T, ← Nat.div_div_eq_div_mul, Nat.add_comm, Nat.mul_comm (3 ^ p),
      Nat.add_mul_div_right _ _ hT, Nat.div_eq_of_lt hρlt, zero_add]

theorem dg_lin (α β X Y p : ℕ) :
    dg (α * X + β * Y) p = (α * dg X p + β * dg Y p + carry α β X Y p) % 3 := by
  have h := (lin_mod_pow_succ α β X Y p).1
  rw [mod_pow_succ_dg] at h
  have hT : 0 < 3 ^ p := by positivity
  exact Nat.eq_of_mul_eq_mul_left hT (by omega)

theorem carry_succ (α β X Y p : ℕ) :
    carry α β X Y (p + 1) = (α * dg X p + β * dg Y p + carry α β X Y p) / 3 :=
  (lin_mod_pow_succ α β X Y p).2

/-! ### Boolean words -/

/-- A Boolean ternary word: every digit is `0` or `1`. -/
def Bool3 (X : ℕ) : Prop := ∀ p, dg X p ≤ 1

theorem bool3_zero : Bool3 0 := fun p => by simp

theorem bool3_pow (k : ℕ) : Bool3 (3 ^ k) := fun p => by rw [dg_pow]; split_ifs <;> omega

theorem Bool3.div_pow {X : ℕ} (hX : Bool3 X) (s : ℕ) : Bool3 (X / 3 ^ s) := fun p => by
  rw [dg_div_pow]; exact hX _

theorem Bool3.mod_pow {X : ℕ} (hX : Bool3 X) (s : ℕ) : Bool3 (X % 3 ^ s) := fun p => by
  rcases Nat.lt_or_ge p s with h | h
  · rw [dg_mod_pow_of_lt _ h]; exact hX p
  · rw [dg_mod_pow_of_ge _ h]; omega

theorem Bool3.mul_pow {X : ℕ} (hX : Bool3 X) (s : ℕ) : Bool3 (3 ^ s * X) := fun p => by
  rcases Nat.lt_or_ge p s with h | h
  · rw [dg_mul_pow_of_lt _ h]; omega
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [dg_mul_pow_add]; exact hX k

theorem Bool3.add {X Y : ℕ} (h : ∀ p, dg X p + dg Y p ≤ 1) : Bool3 (X + Y) := fun p => by
  rw [dg_add_of_le_two (fun p => by have := h p; omega)]; exact h p

theorem bool3_val {c : ℕ → ℕ} (hc : ∀ p, c p ≤ 1) (n : ℕ) : Bool3 (val c n) := fun p => by
  rcases Nat.lt_or_ge p n with h | h
  · rw [dg_val (fun p => by have := hc p; omega) h]; exact hc p
  · rw [dg_val_of_ge (fun p => by have := hc p; omega) h]; omega

theorem dg_rep (n p : ℕ) : dg (rep n) p = if p < n then 1 else 0 := by
  have e : ∀ n, rep n = val (fun _ => 1) n := by
    intro n; induction n with
    | zero => simp [rep_zero, val_zero]
    | succ n ih => rw [rep_succ, val_succ, ih]; ring
  rw [e]
  split_ifs with h
  · exact dg_val (fun _ => by norm_num) h
  · exact dg_val_of_ge (fun _ => by norm_num) (by omega)

theorem bool3_rep (n : ℕ) : Bool3 (rep n) := fun p => by rw [dg_rep]; split_ifs <;> omega

/-- A Boolean word below `3^n` is at most the repunit. -/
theorem Bool3.le_rep {X : ℕ} (hX : Bool3 X) {n : ℕ} (h : X < 3 ^ n) : X ≤ rep n := by
  rw [← val_dg h]
  clear h
  induction n with
  | zero => simp [val_zero, rep_zero]
  | succ n ih =>
    rw [val_succ, rep_succ]
    have := Nat.mul_le_mul_right (3 ^ n) (hX n)
    omega

theorem Bool3.mod_le_rep {X : ℕ} (hX : Bool3 X) (n : ℕ) : X % 3 ^ n ≤ rep n :=
  (hX.mod_pow n).le_rep (Nat.mod_lt _ (by positivity))

/-- The carries of a sum of two Boolean words are at most one. -/
theorem carry_le_one {X Y : ℕ} (hX : Bool3 X) (hY : Bool3 Y) : ∀ p, carry 1 1 X Y p ≤ 1
  | 0 => by simp
  | p + 1 => by
    rw [carry_succ]
    have := hX p; have := hY p; have := carry_le_one hX hY p
    omega

/-- Two Boolean summands of a Boolean sum are digitwise disjoint. -/
theorem bool3_add_disjoint {X Y : ℕ} (hX : Bool3 X) (hY : Bool3 Y) (hXY : Bool3 (X + Y)) :
    ∀ p, dg X p + dg Y p ≤ 1 := by
  -- the carries vanish and the digit sums stay below two
  have key : ∀ p, carry 1 1 X Y p = 0 ∧ dg X p + dg Y p ≤ 1 := by
    intro p
    induction p with
    | zero =>
      refine ⟨by simp, ?_⟩
      have h := hXY 0
      rw [show X + Y = 1 * X + 1 * Y by ring, dg_lin, carry_zero] at h
      have := hX 0; have := hY 0
      omega
    | succ p ih =>
      have hc : carry 1 1 X Y (p + 1) = 0 := by
        rw [carry_succ, ih.1]; have := ih.2; omega
      refine ⟨hc, ?_⟩
      have h := hXY (p + 1)
      rw [show X + Y = 1 * X + 1 * Y by ring, dg_lin, hc] at h
      have := hX (p + 1); have := hY (p + 1)
      omega
  exact fun p => (key p).2

/-! ### Base-`q` chunks, `q = 3^e` -/

/-- A chunk of a Boolean word is Boolean and at most `rep e = (q − 1)/2`. -/
theorem Bool3.chunk_le {X e i : ℕ} (hX : Bool3 X) : X / 3 ^ (e * i) % 3 ^ e ≤ rep e :=
  ((hX.div_pow _).mod_pow e).le_rep (Nat.mod_lt _ (by positivity))

/-- The signed-field decoding step: if the Boolean word `P` is `f + q P'` with
`−q/2 < f < q`, then `f` is the lowest chunk of `P` and `P'` the rest. -/
theorem chunk_step {e P : ℕ} (hP : Bool3 P) {f P' : ℤ}
    (hsum : (P : ℤ) = f + (3 ^ e : ℕ) * P') (hlo : -((3 ^ e : ℕ) : ℤ) < 2 * f)
    (hhi : f < (3 ^ e : ℕ)) :
    f = ((P % 3 ^ e : ℕ) : ℤ) ∧ P' = ((P / 3 ^ e : ℕ) : ℤ) := by
  have hq : (0 : ℤ) < (3 ^ e : ℕ) := by positivity
  have hrep : P % 3 ^ e ≤ rep e := hP.mod_le_rep e
  have hrep2 := two_mul_rep_add_one e
  have hmod := Nat.div_add_mod P (3 ^ e)
  have hmodZ : (P : ℤ) = (3 ^ e : ℕ) * ((P / 3 ^ e : ℕ) : ℤ) + ((P % 3 ^ e : ℕ) : ℤ) := by
    exact_mod_cast hmod.symm
  have hmodlt : ((P % 3 ^ e : ℕ) : ℤ) ≤ (rep e : ℤ) := by exact_mod_cast hrep
  have hrepZ : 2 * (rep e : ℤ) + 1 = (3 ^ e : ℕ) := by exact_mod_cast hrep2
  -- `f ≡ P mod q`, so `f − (P mod q)` is a multiple of `q` in `(−q, q)`
  have hdiff : f - ((P % 3 ^ e : ℕ) : ℤ) = (3 ^ e : ℕ) * (((P / 3 ^ e : ℕ) : ℤ) - P') := by
    linear_combination hmodZ - hsum
  have hf0 : 0 ≤ f := by
    by_contra hneg
    push Not at hneg
    -- then `f + q = P mod q > q/2`, impossible for a Boolean chunk
    have h1 : f - ((P % 3 ^ e : ℕ) : ℤ) < 0 := by
      have : (0 : ℤ) ≤ ((P % 3 ^ e : ℕ) : ℤ) := by positivity
      linarith
    have h2 : -(2 * ((3 ^ e : ℕ) : ℤ)) < f - ((P % 3 ^ e : ℕ) : ℤ) := by linarith
    have hk : ((P / 3 ^ e : ℕ) : ℤ) - P' = -1 := by
      have h3 : (3 ^ e : ℕ) * (((P / 3 ^ e : ℕ) : ℤ) - P') < 0 := by rw [← hdiff]; exact h1
      have h4 : -(2 * ((3 ^ e : ℕ) : ℤ)) < (3 ^ e : ℕ) * (((P / 3 ^ e : ℕ) : ℤ) - P') := by
        rw [← hdiff]; exact h2
      have h5 : ((P / 3 ^ e : ℕ) : ℤ) - P' < 0 := by
        by_contra h; push Not at h; nlinarith
      have h6 : -2 < ((P / 3 ^ e : ℕ) : ℤ) - P' := by
        by_contra h; push Not at h; nlinarith
      omega
    rw [hk] at hdiff
    linarith
  have hk0 : ((P / 3 ^ e : ℕ) : ℤ) - P' = 0 := by
    have h3 : -((3 ^ e : ℕ) : ℤ) < (3 ^ e : ℕ) * (((P / 3 ^ e : ℕ) : ℤ) - P') := by
      rw [← hdiff]; linarith
    have h4 : (3 ^ e : ℕ) * (((P / 3 ^ e : ℕ) : ℤ) - P') < (3 ^ e : ℕ) := by
      rw [← hdiff]; have : (0 : ℤ) ≤ ((P % 3 ^ e : ℕ) : ℤ) := by positivity
      linarith
    have h5 : -1 < ((P / 3 ^ e : ℕ) : ℤ) - P' := by
      by_contra h; push Not at h; nlinarith
    have h6 : ((P / 3 ^ e : ℕ) : ℤ) - P' < 1 := by
      by_contra h; push Not at h; nlinarith
    omega
  rw [hk0, mul_zero] at hdiff
  exact ⟨by linarith, by linarith⟩

end Ternary

end Jones1980
