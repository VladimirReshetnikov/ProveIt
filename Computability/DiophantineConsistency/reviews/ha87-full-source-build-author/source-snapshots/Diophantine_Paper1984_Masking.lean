import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Bits

/-!
# Jones–Matijasevič 1984, §2: the masking relation `≼`

> **Definition.** `r ≼ s` if and only if each binary digit of `r` is less than or equal to
> the corresponding binary digit of `s`.
>
> **(10)** `a ≼ b ↔ a & b = a`.
> **(12)** `a pow 2 ↔ a > 0 and a ≼ 2a - 1`.
> **Lemma.** `r ≼ s ↔ C(s, r) ≡ 1 (mod 2)`  (from Lucas' theorem).
-/

namespace JM1984

/-- The masking relation: every binary digit of `r` is at most the corresponding digit of `s`. -/
def Mask (r s : ℕ) : Prop := ∀ i, r.testBit i = true → s.testBit i = true

@[inherit_doc] infix:50 " ≼ " => Mask

theorem Mask.refl (a : ℕ) : a ≼ a := fun _ h => h

theorem Mask.trans {a b c : ℕ} (h1 : a ≼ b) (h2 : b ≼ c) : a ≼ c := fun i h => h2 i (h1 i h)

theorem zero_mask (a : ℕ) : 0 ≼ a := fun i h => by simp at h

theorem mask_zero_iff (a : ℕ) : a ≼ 0 ↔ a = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : a.testBit i = true
    · have := h i hi; simp at this
    · simp at hi; simp [hi]
  · rintro rfl; exact Mask.refl 0

/-- (10): `a ≼ b ↔ a & b = a`. -/
theorem mask_iff_land (a b : ℕ) : a ≼ b ↔ a &&& b = a := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    by_cases ha : a.testBit i = true
    · rw [ha, h i ha]; rfl
    · simp at ha; simp [ha]
  · intro h i hi
    have := congrArg (fun n => n.testBit i) h
    simp only [Nat.testBit_land, hi, Bool.true_and] at this
    exact this

/-- Shifting: `r ≼ s ↔ (r % 2 = 1 → s % 2 = 1) ∧ r / 2 ≼ s / 2`. -/
theorem mask_iff_div2 (r s : ℕ) :
    r ≼ s ↔ (r % 2 = 1 → s % 2 = 1) ∧ r / 2 ≼ s / 2 := by
  constructor
  · intro h
    refine ⟨fun hr => ?_, fun i hi => ?_⟩
    · have := h 0 (by simpa [Nat.testBit_zero] using hr)
      simpa [Nat.testBit_zero] using this
    · have := h (i + 1) (by simpa [Nat.testBit_succ] using hi)
      simpa [Nat.testBit_succ] using this
  · rintro ⟨h0, h1⟩ i hi
    cases i with
    | zero =>
      simp only [Nat.testBit_zero] at hi ⊢
      exact by simpa using h0 (by simpa using hi)
    | succ i =>
      simp only [Nat.testBit_succ] at hi ⊢
      exact h1 i hi

/-- `2b` is a mask-superset of `b` only when `b = 0`. -/
theorem mask_two_mul_self_iff (b : ℕ) : b ≼ 2 * b ↔ b = 0 := by
  constructor
  · intro h
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · rfl
      · have h' := (mask_iff_div2 b (2 * b)).1 h
        have hev : b % 2 = 0 := by
          by_contra hodd
          have : b % 2 = 1 := by omega
          have := h'.1 this
          omega
        have hb2 : b / 2 < b := Nat.div_lt_self hb (by norm_num)
        have : 2 * b / 2 = 2 * (b / 2) := by omega
        rw [this] at h'
        have := ih (b / 2) hb2 h'.2
        omega
  · rintro rfl; exact zero_mask 0

/-- (12), forward: a power of two `a = 2^k` satisfies `a ≼ 2a - 1`. -/
theorem two_pow_mask (k : ℕ) : 2 ^ k ≼ 2 * 2 ^ k - 1 := by
  intro i hi
  rw [Nat.testBit_two_pow] at hi
  have hik : k = i := by simpa using hi
  rw [← hik, show 2 * 2 ^ k - 1 = 2 ^ (k + 1) - 1 by ring_nf, Nat.testBit_two_pow_sub_one]
  simp

/-- (12): `a` is a power of two if and only if `0 < a` and `a ≼ 2a - 1`. -/
theorem pow_two_iff_mask (a : ℕ) : (∃ k, a = 2 ^ k) ↔ 0 < a ∧ a ≼ 2 * a - 1 := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨by positivity, two_pow_mask k⟩
  · rintro ⟨ha, h⟩
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      rcases Nat.even_or_odd a with ⟨b, hb⟩ | ⟨b, hb⟩
      · -- a = 2b: bits shift, b ≼ 2b - 1
        subst hb
        have hb0 : 0 < b := by omega
        have h' := (mask_iff_div2 (b + b) (2 * (b + b) - 1)).1 h
        have e1 : (b + b) / 2 = b := by omega
        have e2 : (2 * (b + b) - 1) / 2 = 2 * b - 1 := by omega
        rw [e1, e2] at h'
        obtain ⟨k, hk⟩ := ih b (by omega) hb0 h'.2
        exact ⟨k + 1, by rw [hk]; ring⟩
      · -- a = 2b+1: then b ≼ 2b, so b = 0 and a = 1
        subst hb
        have h' := (mask_iff_div2 (2 * b + 1) (2 * (2 * b + 1) - 1)).1 h
        have e1 : (2 * b + 1) / 2 = b := by omega
        have e2 : (2 * (2 * b + 1) - 1) / 2 = 2 * b := by omega
        rw [e1, e2] at h'
        have := (mask_two_mul_self_iff b).1 h'.2
        exact ⟨0, by omega⟩

/-- Odd binomial coefficients of digits `0` and `1`: `C(s₀, r₀)` with `r₀, s₀ ∈ {0,1}` is
odd unless `s₀ = 0` and `r₀ = 1`. -/
theorem choose_bit_odd (r s : ℕ) :
    (s % 2).choose (r % 2) % 2 = 1 ↔ (r % 2 = 1 → s % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one r with hr | hr <;>
    rcases Nat.mod_two_eq_zero_or_one s with hs | hs <;> simp [hr, hs]

/-- The Lemma of §2 (from Lucas' theorem): `r ≼ s ↔ C(s, r)` is odd. -/
theorem mask_iff_choose_odd (r s : ℕ) : r ≼ s ↔ s.choose r % 2 = 1 := by
  induction s using Nat.strong_induction_on generalizing r with
  | _ s ih =>
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · rw [mask_zero_iff]
      constructor
      · rintro rfl; simp
      · intro h
        by_contra hr
        rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hr)] at h
        simp at h
    · have lucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := s) (k := r)
      have hmod : s.choose r % 2 = ((s % 2).choose (r % 2) * (s / 2).choose (r / 2)) % 2 := lucas
      rw [mask_iff_div2, ih (s / 2) (Nat.div_lt_self hs (by norm_num)) (r / 2), ← choose_bit_odd, hmod,
        Nat.mul_mod]
      constructor
      · rintro ⟨h1, h2⟩; rw [h1, h2]
      · intro h
        rcases Nat.mod_two_eq_zero_or_one ((s % 2).choose (r % 2)) with h1 | h1 <;>
          rcases Nat.mod_two_eq_zero_or_one ((s / 2).choose (r / 2)) with h2 | h2 <;>
          simp [h1, h2] at h ⊢

end JM1984
