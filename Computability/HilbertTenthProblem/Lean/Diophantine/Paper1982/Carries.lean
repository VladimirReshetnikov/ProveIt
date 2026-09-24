import Diophantine.Paper1984.Identities
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

/-!
# Jones 1982, §2: digits, carries and Kummer's theorem (Lemmas 2.1–2.16)

> `σ_B(a)` is the sum of the base-`B` digits of `a` (the weight), `σ = σ_2`; `τ_B(a, b)` is the
> number of carries in the base-`B` addition of `a` and `b`.
>
> **Lemma 2.1.** `σ(a) = τ₂(a, a)`.
> **Lemma 2.2.** `τ₂(a, b) = σ(a) + σ(b) − σ(a + b)`.
> **Lemma 2.3.** `b pow 2 ⟺ σ(b) = 1 ⟺ τ₂(b, b − 1) = 0`.
> **Lemma 2.4.** If `N pow 2` then `σ(Na) = σ(a)` and `τ₂(aN, bN) = τ₂(a, b)`.
> **Lemma 2.5.** If `N pow 2` and `b < N` then `σ(a) + σ(b) = σ(aN + b)`.
> **Lemma 2.6.** If `N pow 2` and `a < N` then `σ(N − 1 − a) = σ(N − 1) − σ(a)`.
> **Lemma 2.7.** If `B pow 2`, `b pow 2`, `b < B`, `0 ≤ v < B`, then `v < b ⟺ τ₂(B − b, v) = 0`.
> **Lemma 2.8.** If `B pow 2` and `|V| < B/2`, then `V = 0 ⟺ τ₂(B/2 + V, B/2 − 1) = 0`.
> **Lemma 2.10.** If `N pow 2`, `S₁, T₁ < N`, then
> `τ₂(S₁, T₁) = 0 ∧ τ₂(S₂, T₂) = 0 ⟺ τ₂(S₁ + S₂N, T₁ + T₂N) = 0`.
> **Lemma 2.11.** The same for `n` blocks.
> **Lemma 2.12.** A carry occurs into the `i`-th place according as
> `[(a+b)/Bⁱ] − [a/Bⁱ] − [b/Bⁱ]` equals `1` or `0`.
> **Lemma 2.13.** `τ_B(a, b) = Σ_{i≥1} ([(a+b)/Bⁱ] − [a/Bⁱ] − [b/Bⁱ])`.
> **Theorem 2.14 (Kummer).** For `B` prime, `τ_B(a, b)` is the exact power of `B` dividing
> `C(a+b, a)`.
> **Lemma 2.15.** `n ≤ σ(R) ⟺ 2ⁿ ∣ C(2R, R)`.
> **Lemma 2.16.** If `N pow 2`, `S, T < N` and `R = S(N² − N) + (T+1)(N² − 1)`, then
> `τ₂(S, T) = 0 ⟺ N² ∣ C(2R, R)`.

The carries are counted as in Lemma 2.12 (`Carry B a b i` is the carry into the `i`-th place),
so that Theorem 2.14 is Mathlib's form of Kummer's theorem (`padicValNat_choose'`, 1852) and
Lemma 2.2 follows from it and Legendre's formula in the digit-sum form
(`sub_one_mul_padicValNat_choose_eq_sub_sum_digits'`).  The lemmas about `τ₂(·,·) = 0` are
proved through `τ₂(a, b) = 0 ⟺ a &&& b = 0` (no common binary digit), which also gives the
form used in Theorem 1: `τ₂(a, b) = 0 ⟺ C(a+b, a)` is odd.  Lemma 2.9 is in `Digits.lean`.
-/

namespace Jones1982

open Nat Finset

/-- `σ_B(a)`: the sum of the base-`B` digits of `a` (the weight of `a`). -/
def σ (B a : ℕ) : ℕ := (Nat.digits B a).sum

/-- A carry into the `i`-th place in the base-`B` addition of `a` and `b`
(the digits below `Bⁱ` add up to at least `Bⁱ`). -/
abbrev Carry (B a b i : ℕ) : Prop := B ^ i ≤ a % B ^ i + b % B ^ i

/-- `τ_B(a, b)`: the number of carries in the base-`B` addition of `a` and `b`
(a carry into the `i`-th place needs `i ≤ a + b`). -/
def τ (B a b : ℕ) : ℕ := #{i ∈ Ico 1 (a + b + 1) | Carry B a b i}

theorem τ_comm (B a b : ℕ) : τ B a b = τ B b a := by
  unfold τ
  rw [add_comm a b]
  congr 1
  ext i
  simp only [mem_filter, Carry, add_comm (a % B ^ i)]

/-! ### Lemmas 2.12–2.14 -/

/-- Lemma 2.12: `[(a+b)/Bⁱ] = [a/Bⁱ] + [b/Bⁱ] + (1 or 0 according as a carry occurs)`. -/
theorem lemma_2_12 {B : ℕ} (hB : 0 < B) (a b i : ℕ) :
    (a + b) / B ^ i = a / B ^ i + b / B ^ i + if Carry B a b i then 1 else 0 := by
  have hp : 0 < B ^ i := pow_pos hB i
  have hra : a % B ^ i < B ^ i := Nat.mod_lt _ hp
  have hrb : b % B ^ i < B ^ i := Nat.mod_lt _ hp
  have hsplit : a + b = B ^ i * (a / B ^ i + b / B ^ i) + (a % B ^ i + b % B ^ i) := by
    have ha := Nat.div_add_mod a (B ^ i)
    have hb := Nat.div_add_mod b (B ^ i)
    rw [Nat.mul_add]; omega
  rw [hsplit, Nat.mul_add_div hp]
  split_ifs with h
  · have : (a % B ^ i + b % B ^ i) / B ^ i = 1 :=
      Nat.div_eq_of_lt_le (by unfold Carry at h; omega) (by omega)
    omega
  · have : (a % B ^ i + b % B ^ i) / B ^ i = 0 := Nat.div_eq_of_lt (by unfold Carry at h; omega)
    omega

/-- No carry occurs into a place `i > a + b`. -/
theorem not_carry_of_lt {B : ℕ} (hB : 2 ≤ B) {a b i : ℕ} (hi : a + b < i) : ¬Carry B a b i := by
  intro h
  have h5 : i < 2 ^ i := Nat.lt_two_pow_self
  have h6 : 2 ^ i ≤ B ^ i := Nat.pow_le_pow_left hB i
  have h7 : a % B ^ i ≤ a := Nat.mod_le a _
  have h8 : b % B ^ i ≤ b := Nat.mod_le b _
  unfold Carry at h
  omega

/-- The count of carries may be taken over any range `Ico 1 b₀` with `b₀ > a + b`. -/
theorem τ_eq_card {B : ℕ} (hB : 2 ≤ B) {a b b0 : ℕ} (hb0 : a + b + 1 ≤ b0) :
    τ B a b = #{i ∈ Ico 1 b0 | Carry B a b i} := by
  unfold τ
  congr 1
  ext i
  simp only [mem_filter, mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, ?_⟩, h3⟩
    by_contra hlt
    exact not_carry_of_lt hB (by omega) h3

/-- Lemma 2.13: the series formula for the number of carries. -/
theorem lemma_2_13 {B : ℕ} (hB : 0 < B) (a b : ℕ) :
    τ B a b = ∑ i ∈ Ico 1 (a + b + 1), ((a + b) / B ^ i - a / B ^ i - b / B ^ i) := by
  unfold τ
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lemma_2_12 hB a b i]
  split_ifs <;> omega

/-- Theorem 2.14 (E. Kummer, 1852): for a prime `B`, `τ_B(a, b)` is the exact multiplicity of
`B` in `C(a+b, a)`.  This is Mathlib's `padicValNat_choose'`. -/
theorem theorem_2_14 {B : ℕ} (hB : B.Prime) (a b : ℕ) :
    τ B a b = padicValNat B ((a + b).choose a) := by
  haveI := Fact.mk hB
  rw [add_comm a b, padicValNat_choose' (n := b) (k := a) (b := a + b + 1)
    (lt_of_le_of_lt (Nat.log_le_self _ _) (by omega))]
  rfl

/-! ### The weight `σ = σ₂` -/

theorem σ_two_zero : σ 2 0 = 0 := by simp [σ]

theorem σ_two_one : σ 2 1 = 1 := by simp [σ]

/-- `σ(n) = (n mod 2) + σ([n/2])`. -/
theorem σ_two_rec (n : ℕ) : σ 2 n = n % 2 + σ 2 (n / 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [σ]
  · rw [σ, Nat.digits_def' (by norm_num) hn, List.sum_cons]; rfl

theorem σ_two_two_mul (n : ℕ) : σ 2 (2 * n) = σ 2 n := by
  rw [σ_two_rec (2 * n)]
  have h1 : (2 * n) % 2 = 0 := by omega
  have h2 : (2 * n) / 2 = n := by omega
  rw [h1, h2, zero_add]

theorem σ_two_two_mul_add_one (n : ℕ) : σ 2 (2 * n + 1) = σ 2 n + 1 := by
  rw [σ_two_rec (2 * n + 1)]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2, add_comm]

/-- The weight is subadditive. -/
theorem σ_two_add_le (a b : ℕ) : σ 2 (a + b) ≤ σ 2 a + σ 2 b := by
  suffices H : ∀ n, ∀ a b, a + b = n → σ 2 (a + b) ≤ σ 2 a + σ 2 b from H _ a b rfl
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih a b hab
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha hb; simp [σ_two_zero]
  rw [σ_two_rec (a + b), σ_two_rec a, σ_two_rec b]
  rcases Nat.lt_or_ge (a % 2 + b % 2) 2 with h | h
  · have h1 : (a + b) / 2 = a / 2 + b / 2 := by omega
    have h2 : (a + b) % 2 = a % 2 + b % 2 := by omega
    rw [h1, h2]
    have := ih (a / 2 + b / 2) (by omega) (a / 2) (b / 2) rfl
    omega
  · have h1 : (a + b) / 2 = a / 2 + b / 2 + 1 := by omega
    have h2 : (a + b) % 2 = 0 := by omega
    rw [h1, h2]
    have h3 := ih (a / 2 + b / 2 + 1) (by omega) (a / 2 + b / 2) 1 rfl
    have h4 := ih (a / 2 + b / 2) (by omega) (a / 2) (b / 2) rfl
    have h5 := σ_two_one
    omega

/-- Lemma 2.2 (in additive form): `τ₂(a, b) + σ(a + b) = σ(a) + σ(b)`. -/
theorem lemma_2_2 (a b : ℕ) : τ 2 a b + σ 2 (a + b) = σ 2 a + σ 2 b := by
  have h := @sub_one_mul_padicValNat_choose_eq_sub_sum_digits' 2 a b ⟨Nat.prime_two⟩
  rw [add_comm b a] at h
  rw [theorem_2_14 Nat.prime_two]
  have hle := σ_two_add_le a b
  simp only [σ] at *
  omega

/-- Lemma 2.1: `σ(a) = τ₂(a, a)`. -/
theorem lemma_2_1 (a : ℕ) : σ 2 a = τ 2 a a := by
  have h := lemma_2_2 a a
  rw [← two_mul, σ_two_two_mul] at h
  omega

/-! ### `τ₂(a, b) = 0` means no common binary digit -/

theorem land_eq_zero_iff (a b : ℕ) :
    a &&& b = 0 ↔ ∀ i, a.testBit i = true → b.testBit i = false := by
  constructor
  · intro h i ha
    have := congrArg (fun n => n.testBit i) h
    simp only [Nat.testBit_and, ha, Bool.true_and, Nat.zero_testBit] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases ha : a.testBit i = true
    · rw [ha, h i ha]; rfl
    · simp only [Bool.not_eq_true] at ha; simp [ha]

/-- A set bit at position `i` means `2ⁱ ≤ x`. -/
theorem two_pow_le_of_testBit {x i : ℕ} (h : x.testBit i = true) : 2 ^ i ≤ x := by
  by_contra hlt
  push Not at hlt
  have := Nat.testBit_lt_two_pow hlt
  rw [this] at h
  exact Bool.false_ne_true h

/-- `τ₂(a, b) = 0` iff `a` and `b` have no common binary digit. -/
theorem τ_two_eq_zero_iff (a b : ℕ) : τ 2 a b = 0 ↔ a &&& b = 0 := by
  rw [τ, Finset.card_eq_zero, Finset.filter_eq_empty_iff, land_eq_zero_iff]
  constructor
  · intro h j ha
    by_contra hb
    simp only [Bool.not_eq_false] at hb
    have h1 : 2 ^ j ≤ a % 2 ^ (j + 1) := by
      apply two_pow_le_of_testBit
      rw [Nat.testBit_mod_two_pow]; simp [ha]
    have h2 : 2 ^ j ≤ b % 2 ^ (j + 1) := by
      apply two_pow_le_of_testBit
      rw [Nat.testBit_mod_two_pow]; simp [hb]
    have h3 : Carry 2 a b (j + 1) := by
      have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
      unfold Carry; omega
    have h4 : j + 1 < 2 ^ (j + 1) := Nat.lt_two_pow_self
    have h5 : a % 2 ^ (j + 1) ≤ a := Nat.mod_le _ _
    have h6 : b % 2 ^ (j + 1) ≤ b := Nat.mod_le _ _
    have h7 : 2 ^ (j + 1) ≤ a % 2 ^ (j + 1) + b % 2 ^ (j + 1) := h3
    exact @h (j + 1) (by simp only [mem_Ico]; omega) h3
  · intro h i _ hc
    have hc' : 2 ^ i ≤ a % 2 ^ i + b % 2 ^ i := hc
    have hab : (a % 2 ^ i) &&& (b % 2 ^ i) = 0 := by
      rw [land_eq_zero_iff]
      intro j hj
      rw [Nat.testBit_mod_two_pow] at hj ⊢
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
      rw [h j hj.2]; simp
    have h1 := JM1984.add_eq_land_add_lor (a % 2 ^ i) (b % 2 ^ i)
    rw [hab, zero_add] at h1
    have h2 : (a % 2 ^ i) ||| (b % 2 ^ i) < 2 ^ i :=
      Nat.or_lt_two_pow (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
    omega

/-- Kummer for `B = 2`, as used in Theorem 1: `τ₂(a, b) = 0 ⟺ C(a+b, a)` is odd. -/
theorem τ_two_eq_zero_iff_odd (a b : ℕ) : τ 2 a b = 0 ↔ Odd ((a + b).choose a) := by
  rw [theorem_2_14 Nat.prime_two, padicValNat.eq_zero_iff]
  have hpos : 0 < (a + b).choose a := Nat.choose_pos (by omega)
  constructor
  · rintro (h | h | h)
    · norm_num at h
    · omega
    · exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)
  · intro h; right; right; exact Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 h)

/-! ### Lemmas 2.3–2.6 -/

theorem σ_two_eq_zero_iff (n : ℕ) : σ 2 n = 0 ↔ n = 0 := by
  constructor
  · intro h
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rfl
    rw [σ_two_rec] at h
    have h1 : n % 2 = 0 := by omega
    have h2 : σ 2 (n / 2) = 0 := by omega
    have := ih (n / 2) (by omega) h2
    omega
  · rintro rfl; exact σ_two_zero

theorem σ_two_pos {n : ℕ} (hn : 0 < n) : 1 ≤ σ 2 n := by
  by_contra h
  have h0 : σ 2 n = 0 := by omega
  have := (σ_two_eq_zero_iff n).1 h0
  omega

theorem σ_two_pow (k : ℕ) : σ 2 (2 ^ k) = 1 := by
  induction k with
  | zero => exact σ_two_one
  | succ k ih => rw [pow_succ, mul_comm, σ_two_two_mul, ih]

/-- Lemma 2.3, first equivalence: `b pow 2 ⟺ σ(b) = 1`. -/
theorem lemma_2_3_σ (b : ℕ) : (∃ k, b = 2 ^ k) ↔ σ 2 b = 1 := by
  constructor
  · rintro ⟨k, rfl⟩; exact σ_two_pow k
  · intro h
    induction b using Nat.strong_induction_on with
    | _ b ih =>
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · rw [σ_two_zero] at h; omega
    rw [σ_two_rec] at h
    rcases Nat.lt_or_ge (b % 2) 1 with h1 | h1
    · have h2 : σ 2 (b / 2) = 1 := by omega
      obtain ⟨k, hk⟩ := ih (b / 2) (by omega) h2
      exact ⟨k + 1, by rw [pow_succ]; omega⟩
    · have h2 : σ 2 (b / 2) = 0 := by omega
      have h3 := (σ_two_eq_zero_iff _).1 h2
      exact ⟨0, by omega⟩

/-- Lemma 2.3, second equivalence: for `b > 0`, `σ(b) = 1 ⟺ τ₂(b, b − 1) = 0`. -/
theorem lemma_2_3_τ {b : ℕ} (hb : 0 < b) : σ 2 b = 1 ↔ τ 2 b (b - 1) = 0 := by
  have h := lemma_2_2 b (b - 1)
  have h1 : b + (b - 1) = 2 * (b - 1) + 1 := by omega
  rw [h1, σ_two_two_mul_add_one] at h
  have h2 := σ_two_pos hb
  omega

/-- Lemma 2.3: `b pow 2 ⟺ τ₂(b, b − 1) = 0` for `b > 0`. -/
theorem lemma_2_3 {b : ℕ} (hb : 0 < b) : (∃ k, b = 2 ^ k) ↔ τ 2 b (b - 1) = 0 :=
  (lemma_2_3_σ b).trans (lemma_2_3_τ hb)

/-- Lemma 2.4, first part: `σ(2ᵏ a) = σ(a)`. -/
theorem lemma_2_4_σ (k a : ℕ) : σ 2 (2 ^ k * a) = σ 2 a := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_comm (2 ^ k) 2, mul_assoc, σ_two_two_mul, ih]

/-- Lemma 2.4, second part: `τ₂(2ᵏ a, 2ᵏ b) = τ₂(a, b)`. -/
theorem lemma_2_4_τ (k a b : ℕ) : τ 2 (2 ^ k * a) (2 ^ k * b) = τ 2 a b := by
  have h1 := lemma_2_2 (2 ^ k * a) (2 ^ k * b)
  have h2 := lemma_2_2 a b
  rw [← mul_add, lemma_2_4_σ, lemma_2_4_σ, lemma_2_4_σ] at h1
  omega

theorem lemma_2_4_τ' (k a b : ℕ) : τ 2 (a * 2 ^ k) (b * 2 ^ k) = τ 2 a b := by
  rw [mul_comm a, mul_comm b, lemma_2_4_τ]

/-- Lemma 2.5: if `b < 2ᵏ` then `σ(a 2ᵏ + b) = σ(a) + σ(b)`. -/
theorem lemma_2_5 {k b : ℕ} (hb : b < 2 ^ k) (a : ℕ) :
    σ 2 (a * 2 ^ k + b) = σ 2 a + σ 2 b := by
  induction k generalizing b with
  | zero =>
    have : b = 0 := by simpa using hb
    subst this; simp [σ_two_zero]
  | succ k ih =>
    have hx : a * 2 ^ (k + 1) = 2 * (a * 2 ^ k) := by ring
    have hx' : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have h1 : a * 2 ^ (k + 1) + b = 2 * (a * 2 ^ k + b / 2) + b % 2 := by omega
    rw [h1, σ_two_rec (2 * _ + _)]
    have h2 : (2 * (a * 2 ^ k + b / 2) + b % 2) % 2 = b % 2 := by omega
    have h3 : (2 * (a * 2 ^ k + b / 2) + b % 2) / 2 = a * 2 ^ k + b / 2 := by omega
    rw [h2, h3, ih (by omega), σ_two_rec b]
    ring

/-- Lemma 2.6: if `a < 2ᵏ` then `σ(2ᵏ − 1 − a) + σ(a) = k = σ(2ᵏ − 1)`. -/
theorem lemma_2_6 {k a : ℕ} (ha : a < 2 ^ k) : σ 2 (2 ^ k - 1 - a) + σ 2 a = k := by
  induction k generalizing a with
  | zero =>
    have : a = 0 := by simpa using ha
    subst this; simp [σ_two_zero]
  | succ k ih =>
    have hx : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hp : 0 < 2 ^ k := by positivity
    have h1 : 2 ^ (k + 1) - 1 - a = 2 * (2 ^ k - 1 - a / 2) + (1 - a % 2) := by omega
    rw [h1, σ_two_rec (2 * _ + _), σ_two_rec a]
    have h2 : (2 * (2 ^ k - 1 - a / 2) + (1 - a % 2)) % 2 = 1 - a % 2 := by omega
    have h3 : (2 * (2 ^ k - 1 - a / 2) + (1 - a % 2)) / 2 = 2 ^ k - 1 - a / 2 := by omega
    rw [h2, h3]
    have := ih (a := a / 2) (by omega)
    omega

theorem σ_two_pow_sub_one (k : ℕ) : σ 2 (2 ^ k - 1) = k := by
  have := lemma_2_6 (k := k) (a := 0) (by positivity)
  rw [σ_two_zero] at this
  simpa using this

/-! ### Lemmas 2.7, 2.8 -/

/-- The binary digits of `2ᴷ − 2ᵏ` (`k ≤ K`) are the positions `k ≤ i < K`. -/
theorem testBit_two_pow_sub_two_pow {k K : ℕ} (hkK : k ≤ K) (i : ℕ) :
    (2 ^ K - 2 ^ k).testBit i = decide (k ≤ i ∧ i < K) := by
  have h : 2 ^ K - 2 ^ k = (2 ^ (K - k) - 1) * 2 ^ k := by
    rw [Nat.sub_mul, one_mul, ← pow_add, Nat.sub_add_cancel hkK]
  have e1 : (decide (k ≤ i) && decide (i - k < K - k)) = decide (k ≤ i ∧ i < K) := by
    by_cases hk : k ≤ i
    · by_cases hi : i < K
      · have : i - k < K - k := by omega
        simp [hk, hi, this]
      · have : ¬ (i - k < K - k) := by omega
        simp [hk, hi, this]
    · simp [hk]
  rw [h, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one, e1]

/-- Lemma 2.7: for `k ≤ K` and `v < 2ᴷ`, `v < 2ᵏ ⟺ τ₂(2ᴷ − 2ᵏ, v) = 0`. -/
theorem lemma_2_7 {k K v : ℕ} (hkK : k ≤ K) (hv : v < 2 ^ K) :
    v < 2 ^ k ↔ τ 2 (2 ^ K - 2 ^ k) v = 0 := by
  rw [τ_two_eq_zero_iff, land_eq_zero_iff]
  simp only [testBit_two_pow_sub_two_pow hkK, decide_eq_true_eq]
  constructor
  · intro h i ⟨hki, _⟩
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hki))
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_cases hiK : i < K
    · exact h i ⟨hi, hiK⟩
    · exact Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- Lemma 2.7, the special case `b = 1`: for `v < 2ᴷ`, `v = 0 ⟺ τ₂(2ᴷ − 1, v) = 0`. -/
theorem lemma_2_7' {K v : ℕ} (hv : v < 2 ^ K) : v = 0 ↔ τ 2 (2 ^ K - 1) v = 0 := by
  have := lemma_2_7 (k := 0) (Nat.zero_le K) hv
  simp only [pow_zero, Nat.lt_one_iff] at this
  exact this

/-- Lemma 2.8: for `0 < x < 2ᴷ` (`K ≥ 1`), `x = 2ᴷ⁻¹ ⟺ τ₂(x, 2ᴷ⁻¹ − 1) = 0`
(the article writes `x = B/2 + V` with `|V| < B/2`). -/
theorem lemma_2_8 {K x : ℕ} (hK : 1 ≤ K) (hx0 : 0 < x) (hx : x < 2 ^ K) :
    x = 2 ^ (K - 1) ↔ τ 2 x (2 ^ (K - 1) - 1) = 0 := by
  rw [τ_two_eq_zero_iff, Nat.and_two_pow_sub_one_eq_mod]
  have h2 : 2 ^ K = 2 * 2 ^ (K - 1) := by
    rw [← pow_succ']; congr 1; omega
  constructor
  · intro h; rw [h]; exact Nat.mod_self _
  · intro h
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h
    have hp : 0 < 2 ^ (K - 1) := by positivity
    have hq1 : q = 1 := by
      rcases Nat.lt_or_ge q 2 with hq2 | hq2
      · interval_cases q <;> omega
      · exfalso; have := Nat.mul_le_mul_left (2 ^ (K - 1)) hq2; omega
    rw [hq, hq1, mul_one]

/-- Lemma 2.8 with the article's signed `V`: for `|V| < 2ᴷ⁻¹`,
`V = 0 ⟺ τ₂(2ᴷ⁻¹ + V, 2ᴷ⁻¹ − 1) = 0`. -/
theorem lemma_2_8' {K : ℕ} (hK : 1 ≤ K) {V : ℤ} (hV : |V| < 2 ^ (K - 1)) :
    V = 0 ↔ τ 2 ((2 ^ (K - 1) : ℤ) + V).toNat (2 ^ (K - 1) - 1) = 0 := by
  have h2 : (2 : ℤ) ^ K = 2 * 2 ^ (K - 1) := by
    conv_lhs => rw [show K = (K - 1) + 1 by omega]
    rw [pow_succ]; ring
  have hpos : 0 < (2 ^ (K - 1) : ℤ) + V := by
    have := abs_lt.1 hV; linarith
  have hlt : (2 ^ (K - 1) : ℤ) + V < 2 ^ K := by
    have := abs_lt.1 hV; linarith
  rw [← lemma_2_8 hK (by omega) (by
    have := Int.toNat_of_nonneg hpos.le
    have h3 : (((2 ^ (K - 1) : ℤ) + V).toNat : ℤ) < 2 ^ K := by rw [this]; exact hlt
    exact_mod_cast h3)]
  constructor
  · rintro rfl
    have : ((2 ^ (K - 1) : ℕ) : ℤ) = 2 ^ (K - 1) := by push_cast; rfl
    rw [add_zero, ← this, Int.toNat_natCast]
  · intro h
    have := Int.toNat_of_nonneg hpos.le
    rw [h] at this
    push_cast at this
    linarith

/-! ### Lemmas 2.10, 2.11 -/

/-- Blockwise `&&&`: for `S₁, T₁ < 2ᵏ`,
`(S₁ + S₂ 2ᵏ) &&& (T₁ + T₂ 2ᵏ) = (S₁ &&& T₁) + (S₂ &&& T₂) 2ᵏ`. -/
theorem land_add_mul_two_pow {k S₁ S₂ T₁ T₂ : ℕ} (hS : S₁ < 2 ^ k) (hT : T₁ < 2 ^ k) :
    (S₁ + S₂ * 2 ^ k) &&& (T₁ + T₂ * 2 ^ k) = (S₁ &&& T₁) + (S₂ &&& T₂) * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, JM1984.testBit_add_mul_two_pow hS, JM1984.testBit_add_mul_two_pow hT,
    JM1984.testBit_add_mul_two_pow (Nat.and_lt_two_pow _ hT), Nat.testBit_and, Nat.testBit_and]
  split_ifs <;> rfl

/-- Lemma 2.10: for `S₁, T₁ < 2ᵏ`,
`τ₂(S₁, T₁) = 0 ∧ τ₂(S₂, T₂) = 0 ⟺ τ₂(S₁ + S₂ 2ᵏ, T₁ + T₂ 2ᵏ) = 0`. -/
theorem lemma_2_10 {k S₁ S₂ T₁ T₂ : ℕ} (hS : S₁ < 2 ^ k) (hT : T₁ < 2 ^ k) :
    (τ 2 S₁ T₁ = 0 ∧ τ 2 S₂ T₂ = 0) ↔ τ 2 (S₁ + S₂ * 2 ^ k) (T₁ + T₂ * 2 ^ k) = 0 := by
  simp only [τ_two_eq_zero_iff]
  rw [land_add_mul_two_pow hS hT]
  have hp : 0 < 2 ^ k := by positivity
  constructor
  · rintro ⟨h1, h2⟩; rw [h1, h2]; simp
  · intro h
    have h1 : S₁ &&& T₁ = 0 := by omega
    have h2 : (S₂ &&& T₂) * 2 ^ k = 0 := by omega
    rcases Nat.mul_eq_zero.1 h2 with h2 | h2
    · exact ⟨h1, h2⟩
    · omega

/-- Lemma 2.11 for lists of blocks in a common base `2ᵗ` (digit lists of equal length with
digits `< 2ᵗ`): `τ₂(S, T) = 0` iff `τ₂(Sᵢ, Tᵢ) = 0` for all `i`. -/
theorem lemma_2_11 {t : ℕ} : ∀ (L M : List ℕ), (∀ x ∈ L, x < 2 ^ t) → (∀ x ∈ M, x < 2 ^ t) →
    L.length = M.length →
    (τ 2 (ofDigits (2 ^ t) L) (ofDigits (2 ^ t) M) = 0 ↔
      List.Forall₂ (fun x y => τ 2 x y = 0) L M)
  | [], [], _, _, _ => by simp [ofDigits, τ]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: L, y :: M, hL, hM, hlen => by
    simp only [ofDigits_cons, List.forall₂_cons]
    rw [mul_comm (2 ^ t) (ofDigits _ L), mul_comm (2 ^ t) (ofDigits _ M)]
    rw [← lemma_2_10 (hL x (by simp)) (hM y (by simp))]
    rw [lemma_2_11 L M (fun z hz => hL z (by simp [hz])) (fun z hz => hM z (by simp [hz]))
      (by simpa using hlen)]

/-- Lemma 2.11 (ii): `S < N` for `N` the product of the block sizes. -/
theorem lemma_2_11_lt {t : ℕ} (ht : 0 < t) {L : List ℕ} (hL : ∀ x ∈ L, x < 2 ^ t) :
    ofDigits (2 ^ t) L < (2 ^ t) ^ L.length :=
  ofDigits_lt_base_pow_length (Nat.one_lt_two_pow_iff.2 ht.ne') hL

/-- Lemma 2.11 for three blocks, in the form used in §4 (U21), (U22):
for `S₁, T₁ < N₁ = 2ᵏ¹` and `S₂, T₂ < N₂ = 2ᵏ²`,
`τ₂(S₁,T₁) = τ₂(S₂,T₂) = τ₂(S₃,T₃) = 0 ⟺ τ₂(S₁ + S₂N₁ + S₃N₁N₂, T₁ + T₂N₁ + T₃N₁N₂) = 0`. -/
theorem lemma_2_11_three {k₁ k₂ S₁ S₂ S₃ T₁ T₂ T₃ : ℕ} (hS₁ : S₁ < 2 ^ k₁) (hT₁ : T₁ < 2 ^ k₁)
    (hS₂ : S₂ < 2 ^ k₂) (hT₂ : T₂ < 2 ^ k₂) :
    (τ 2 S₁ T₁ = 0 ∧ τ 2 S₂ T₂ = 0 ∧ τ 2 S₃ T₃ = 0) ↔
      τ 2 (S₁ + S₂ * 2 ^ k₁ + S₃ * 2 ^ k₁ * 2 ^ k₂) (T₁ + T₂ * 2 ^ k₁ + T₃ * 2 ^ k₁ * 2 ^ k₂) = 0 := by
  rw [show S₁ + S₂ * 2 ^ k₁ + S₃ * 2 ^ k₁ * 2 ^ k₂ = S₁ + (S₂ + S₃ * 2 ^ k₂) * 2 ^ k₁ by ring,
    show T₁ + T₂ * 2 ^ k₁ + T₃ * 2 ^ k₁ * 2 ^ k₂ = T₁ + (T₂ + T₃ * 2 ^ k₂) * 2 ^ k₁ by ring,
    ← lemma_2_10 hS₁ hT₁, ← lemma_2_10 hS₂ hT₂]

/-! ### Lemmas 2.15, 2.16 -/

/-- Lemma 2.15: `n ≤ σ(R) ⟺ 2ⁿ ∣ C(2R, R)`. -/
theorem lemma_2_15 (n R : ℕ) : n ≤ σ 2 R ↔ 2 ^ n ∣ (2 * R).choose R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : (2 * R).choose R = (R + R).choose R := by rw [two_mul]
  rw [h, padicValNat_dvd_iff_le (Nat.choose_pos (by omega)).ne', ← theorem_2_14 Nat.prime_two,
    ← lemma_2_1]

/-- Lemma 2.16: for `N = 2^α`, `S, T < N` and `R = S(N² − N) + (T + 1)(N² − 1)`,
`τ₂(S, T) = 0 ⟺ N² ∣ C(2R, R)`. -/
theorem lemma_2_16 {α S T R : ℕ} (hS : S < 2 ^ α) (hT : T < 2 ^ α)
    (hR : R = S * ((2 ^ α) ^ 2 - 2 ^ α) + (T + 1) * ((2 ^ α) ^ 2 - 1)) :
    τ 2 S T = 0 ↔ (2 ^ α) ^ 2 ∣ (2 * R).choose R := by
  obtain ⟨N, hN⟩ : ∃ N, N = 2 ^ α := ⟨_, rfl⟩
  rw [← hN] at hS hT hR ⊢
  have h1N : 1 ≤ N := by rw [hN]; exact Nat.one_le_two_pow
  have hNN : N ≤ N ^ 2 := by nlinarith
  have hS1 : S ≤ N - 1 := by omega
  have hT1 : T ≤ N - 1 := by omega
  have hR' : R = ((S + T) * N + (N - 1 - S)) * N + (N - 1 - T) := by
    rw [hR]
    zify [hS1, hT1, h1N, hNN, (by omega : 1 ≤ N ^ 2)]
    ring
  have h2 : N ^ 2 = 2 ^ (2 * α) := by rw [hN, ← pow_mul, mul_comm]
  rw [h2, ← lemma_2_15]
  have hσ : σ 2 R = σ 2 (S + T) + σ 2 (N - 1 - S) + σ 2 (N - 1 - T) := by
    rw [hR', hN, lemma_2_5 (by rw [← hN]; omega), lemma_2_5 (by rw [← hN]; omega)]
  have h6S := lemma_2_6 (k := α) (a := S) (by rw [← hN]; exact hS)
  have h6T := lemma_2_6 (k := α) (a := T) (by rw [← hN]; exact hT)
  rw [← hN] at h6S h6T
  have h22 := lemma_2_2 S T
  omega

end Jones1982
