import Diophantine.Paper1980.TernaryDigits

/-!
# Leading ternary trits

`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §4.  The borrow exclusions of the counter
route are decided by the *lowest nonzero ternary digit* of the numbers involved.

`Lead p t X` says that digit is `t`, at position `p`; equivalently `X = 3^p Y` with
`Y ≡ t (mod 3)`.  The facts the note uses are:

* the position and the digit are determined by `X` (`Lead.unique`), so two readings of
  the same number must agree;
* a product of a `1`-led and a `2`-led number is `2`-led (`Lead.mul`) — this is how the
  fixed table `K`, whose minimal exponent is unique with coefficient one, transfers the
  leading `2` of the doubled state word `C` to `KC`;
* twice a Boolean word is `2`-led (`lead_two_of_bool`) while its odd successor `2v + 1`
  is `1`-led (`lead_one_of_odd`): adding one to a `0/2` word clears its initial run of
  twos and turns the next zero into a one.  So a `2`-led number is never of the form
  `2v + 1` with `v` Boolean (`Lead.not_two_odd`), which is exactly the borrow exclusion.

`chunk_step_even` is the companion decoding step for *doubled* packed words.  A Boolean
word's chunks are at most `rep e`, so a doubled word's chunks are even and at most
`q − 1`; an even conceptual field in `(−q, q)` therefore cannot have borrowed, since a
borrow would subtract the odd number `q` from an even chunk.
-/

namespace Jones1980

namespace Ternary

/-- `Lead p t X`: the lowest nonzero ternary digit of `X` is `t`, at position `p`. -/
def Lead (p t X : ℕ) : Prop := ∃ Y, X = 3 ^ p * Y ∧ Y % 3 = t

/-- Every positive number has a leading trit. -/
theorem exists_lead : ∀ {X : ℕ}, 0 < X → ∃ p Y, X = 3 ^ p * Y ∧ Y % 3 ≠ 0 := by
  intro X
  induction X using Nat.strong_induction_on with
  | _ X ih =>
    intro hX
    rcases Nat.eq_zero_or_pos (X % 3) with h0 | h0
    · obtain ⟨X', rfl⟩ : 3 ∣ X := Nat.dvd_of_mod_eq_zero h0
      have hX' : 0 < X' := by omega
      obtain ⟨p, Y, hY, hY3⟩ := ih X' (by omega) hX'
      exact ⟨p + 1, Y, by rw [hY, pow_succ]; ring, hY3⟩
    · exact ⟨0, X, by simp, by omega⟩

theorem Lead.digit {p t X : ℕ} (h : Lead p t X) : X / 3 ^ p % 3 = t := by
  obtain ⟨Y, rfl, hY⟩ := h
  rw [Nat.mul_div_cancel_left _ (by positivity)]
  exact hY

theorem Lead.below {p t X i : ℕ} (h : Lead p t X) (hi : i < p) : X / 3 ^ i % 3 = 0 := by
  obtain ⟨Y, rfl, -⟩ := h
  have hsp : (3 : ℕ) ^ p = 3 ^ i * 3 ^ (p - i) := by rw [← pow_add]; congr 1; omega
  have hdiv : 3 ^ p * Y / 3 ^ i = 3 ^ (p - i) * Y := by
    rw [hsp, mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
  rw [hdiv, show p - i = (p - i - 1) + 1 by omega, pow_succ,
    show (3 : ℕ) ^ (p - i - 1) * 3 * Y = 3 * (3 ^ (p - i - 1) * Y) by ring, Nat.mul_mod_right]

theorem Lead.pos {p t X : ℕ} (h : Lead p t X) (ht : t ≠ 0) : 0 < X := by
  obtain ⟨Y, rfl, hY⟩ := h
  have hYpos : 0 < Y := by omega
  positivity

/-- The leading position and the leading digit are determined by the number. -/
theorem Lead.unique {p p' s t X : ℕ} (h1 : Lead p s X) (h2 : Lead p' t X)
    (hs : s ≠ 0) (ht : t ≠ 0) : p = p' ∧ s = t := by
  have hpp : p = p' := by
    rcases lt_trichotomy p p' with h | h | h
    · exact absurd (h1.digit.symm.trans (h2.below h)) hs
    · exact h
    · exact absurd (h2.digit.symm.trans (h1.below h)) ht
  subst hpp
  exact ⟨rfl, h1.digit.symm.trans h2.digit⟩

/-- A `1`-led factor carries a `2`-led factor's leading digit. -/
theorem Lead.mul {p p' X Y : ℕ} (h1 : Lead p 1 X) (h2 : Lead p' 2 Y) :
    Lead (p + p') 2 (X * Y) := by
  obtain ⟨A, rfl, hA⟩ := h1
  obtain ⟨B, rfl, hB⟩ := h2
  refine ⟨A * B, by rw [pow_add]; ring, ?_⟩
  rw [Nat.mul_mod, hA, hB]

/-- The leading trit is visible modulo `3^(p+1)`. -/
theorem Lead.of_modEq {p t X V : ℕ} (h : Lead p t X)
    (hmod : V % 3 ^ (p + 1) = X % 3 ^ (p + 1)) : Lead p t V := by
  obtain ⟨Y, hXY, hY⟩ := h
  have ht3 : t < 3 := by omega
  have hX : X % 3 ^ (p + 1) = 3 ^ p * t := by
    rw [hXY, pow_succ, Nat.mul_mod_mul_left, hY]
  refine ⟨3 * (V / 3 ^ (p + 1)) + t, ?_, by omega⟩
  have key : 3 ^ (p + 1) * (V / 3 ^ (p + 1)) + 3 ^ p * t = V := by
    rw [← hX, ← hmod]; exact Nat.div_add_mod V (3 ^ (p + 1))
  conv_lhs => rw [← key]
  rw [pow_succ]; ring

/-- Twice a positive Boolean word is `2`-led. -/
theorem lead_two_of_bool {b : ℕ} (hb : Bool3 b) (hpos : 0 < b) : ∃ p, Lead p 2 (2 * b) := by
  obtain ⟨p, Y, hY, hY3⟩ := exists_lead hpos
  have hdig : b / 3 ^ p % 3 = Y % 3 := by rw [hY, Nat.mul_div_cancel_left _ (by positivity)]
  have hbp : b / 3 ^ p % 3 ≤ 1 := hb p
  have h1 : Y % 3 = 1 := by omega
  exact ⟨p, 2 * Y, by rw [hY]; ring, by rw [Nat.mul_mod, h1]⟩

/-- The odd successor of a Boolean word is `1`-led: adding one clears the initial run of
twos and turns the next zero into a one. -/
theorem lead_one_of_odd {v : ℕ} (hv : Bool3 v) : ∃ p, Lead p 1 (2 * v + 1) := by
  obtain ⟨j, Y, hY, hY3⟩ := exists_lead (X := 2 * v + 1) (by omega)
  have hq : 0 < (3 : ℕ) ^ j := by positivity
  have hmod : (2 * v + 1) % 3 ^ j = 0 := by rw [hY]; exact Nat.mul_mod_right _ _
  have hdm := Nat.div_add_mod v (3 ^ j)
  have hx : 3 ^ j * (2 * (v / 3 ^ j)) = 2 * (3 ^ j * (v / 3 ^ j)) := by ring
  have hsplit : 2 * v + 1 = 3 ^ j * (2 * (v / 3 ^ j)) + (2 * (v % 3 ^ j) + 1) := by omega
  have hzero : (2 * (v % 3 ^ j) + 1) % 3 ^ j = 0 := by
    rw [hsplit, Nat.mul_add_mod] at hmod; exact hmod
  have hw := hv.mod_le_rep j
  have hrep := two_mul_rep_add_one j
  have heq : 2 * (v % 3 ^ j) + 1 = 3 ^ j := by
    rcases Nat.lt_or_ge (2 * (v % 3 ^ j) + 1) (3 ^ j) with h | h
    · rw [Nat.mod_eq_of_lt h] at hzero; omega
    · omega
  have hYeq : Y = 2 * (v / 3 ^ j) + 1 := by
    have hmul : 3 ^ j * Y = 3 ^ j * (2 * (v / 3 ^ j) + 1) := by
      rw [← hY, hsplit, heq]; ring
    exact Nat.eq_of_mul_eq_mul_left hq hmul
  have hd : v / 3 ^ j % 3 ≤ 1 := hv j
  exact ⟨j, Y, hY, by omega⟩

/-- A `2`-led number is never the odd successor of a Boolean word. -/
theorem Lead.not_two_odd {p v : ℕ} (hv : Bool3 v) (h : Lead p 2 (2 * v + 1)) : False := by
  obtain ⟨j, hj⟩ := lead_one_of_odd hv
  have h12 := (h.unique hj (by norm_num) (by norm_num)).2
  omega

/-! ### Decoding a doubled packed word -/

/-- The decoding step for a *doubled* Boolean word.  An even conceptual field in `(−q, q)`
is its own chunk: a borrow would subtract the odd `q` from an even chunk. -/
theorem chunk_step_even {e B : ℕ} (hB : Bool3 B) {f P' : ℤ}
    (hsum : 2 * (B : ℤ) = f + ((3 ^ e : ℕ) : ℤ) * P')
    (hlo : -((3 ^ e : ℕ) : ℤ) < f) (hhi : f < ((3 ^ e : ℕ) : ℤ)) (heven : 2 ∣ f) :
    f = ((2 * (B % 3 ^ e) : ℕ) : ℤ) ∧ P' = ((2 * (B / 3 ^ e) : ℕ) : ℤ) := by
  have hq : (0 : ℤ) < ((3 ^ e : ℕ) : ℤ) := by positivity
  have hrep := two_mul_rep_add_one e
  have hmodle := hB.mod_le_rep e
  have hdm := Nat.div_add_mod B (3 ^ e)
  have hx : 3 ^ e * (2 * (B / 3 ^ e)) = 2 * (3 ^ e * (B / 3 ^ e)) := by ring
  have hsplitN : 2 * B = 2 * (B % 3 ^ e) + 3 ^ e * (2 * (B / 3 ^ e)) := by omega
  have hsplit : 2 * (B : ℤ)
      = ((2 * (B % 3 ^ e) : ℕ) : ℤ) + ((3 ^ e : ℕ) : ℤ) * ((2 * (B / 3 ^ e) : ℕ) : ℤ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hsplitN
  have hcqN : 2 * (B % 3 ^ e) < 3 ^ e := by omega
  have hcq : ((2 * (B % 3 ^ e) : ℕ) : ℤ) < ((3 ^ e : ℕ) : ℤ) := by exact_mod_cast hcqN
  have hc0 : (0 : ℤ) ≤ ((2 * (B % 3 ^ e) : ℕ) : ℤ) := by positivity
  have hdiff : f - ((2 * (B % 3 ^ e) : ℕ) : ℤ)
      = ((3 ^ e : ℕ) : ℤ) * (((2 * (B / 3 ^ e) : ℕ) : ℤ) - P') := by
    linear_combination hsplit - hsum
  have hk1 : ((2 * (B / 3 ^ e) : ℕ) : ℤ) - P' < 1 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [hdiff, hq, hhi, hc0]
  have hk2 : -2 < ((2 * (B / 3 ^ e) : ℕ) : ℤ) - P' := by
    by_contra hcon
    push_neg at hcon
    nlinarith [hdiff, hq, hlo, hcq]
  have hkz : ((2 * (B / 3 ^ e) : ℕ) : ℤ) - P' = 0 := by
    rcases (show ((2 * (B / 3 ^ e) : ℕ) : ℤ) - P' = 0 ∨ ((2 * (B / 3 ^ e) : ℕ) : ℤ) - P' = -1 by
      omega) with h | h
    · exact h
    · exfalso
      rw [h] at hdiff
      have h2c : (2 : ℤ) ∣ ((2 * (B % 3 ^ e) : ℕ) : ℤ) :=
        ⟨((B % 3 ^ e : ℕ) : ℤ), by push_cast; ring⟩
      have h2q : (2 : ℤ) ∣ ((3 ^ e : ℕ) : ℤ) := by
        have hrw : ((3 ^ e : ℕ) : ℤ) = ((2 * (B % 3 ^ e) : ℕ) : ℤ) - f := by linarith
        rw [hrw]
        exact dvd_sub h2c heven
      have h2n : (2 : ℕ) ∣ 3 ^ e := by exact_mod_cast h2q
      have hodd : (3 : ℕ) ^ e % 2 = 1 := by rw [Nat.pow_mod]; norm_num
      omega
  refine ⟨?_, by linarith⟩
  rw [hkz, mul_zero] at hdiff
  linarith

end Ternary

end Jones1980
