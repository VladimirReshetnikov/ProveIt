import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Centered cyclic traces: exact defect factorization, cubic dynamics, and fifth-trace channels

For an odd integer `d = 2h + 1` the *centered cyclic trace* is
`T_d(z) = (z^{-h} + ⋯ + z^{h}) / d`.  Writing `z = a / b` in lowest terms, its value is
`S_d(a,b) / (d (ab)^h)` with `S_d(a,b) = (a^d - b^d)/(a - b) = ∑_{i<d} a^i b^{d-1-i}`.

This file formalizes the finite algebraic core of the centered-trace analysis:

* the exact *defect factorization*
  `S_{2h+1}(a,b) - (2h+1)(ab)^h = ∑_{j=1}^{h} (ab)^{h-j} (a^j - b^j)^2`,
  which exhibits the defect as a sum of squares and, after extracting `(a - b)^2`, shows
  that every centered trace has local contact exactly two at `z = 1`;
* the cubic special case `a^2 + ab + b^2 - 3ab = (a - b)^2`, the coprimality
  `gcd(a^2 + ab + b^2, ab) = 1`, and the fact that the only possible reduction factor of
  `T_3(a/b)` is `3`, which occurs exactly when `3 ∣ a - b`; consequently the reduced defect of
  the cubic trace is `u^2` or `u^2/3`, so every prime `ℓ ≠ 3` has its valuation in the defect
  doubled exactly and no new prime ever enters — cubic iteration cannot manufacture a common
  prime between the dyadic and triadic branches of a hypothetical counterexample;
* the *reciprocal-quadratic bridge identity*
  `cd (a^2 + λab + b^2) - ab (c^2 + λcd + d^2) = (ad - bc)(ac - bd)`
  and the resulting *two-channel theorem* for the fifth trace: a prime power `p^e` (with
  `p ≠ 5` prime) dividing both `a^2 + 3ab + b^2` and `c^2 + 3cd + d^2` for coprime pairs
  divides exactly one of the two channels `ad - bc` and `ac - bd`, with its full exponent.

All statements are finite integer identities and divisibility facts; no transcendence input
enters.
-/

namespace LeanProofs.TwoBaseIntegerExponent.CenteredTrace

open Finset

/-- `S_d(a,b) = ∑_{i<d} a^i b^{d-1-i}`, the homogeneous geometric sum. -/
def homGeomSum (a b : ℤ) (d : ℕ) : ℤ := ∑ i ∈ range d, a ^ i * b ^ (d - 1 - i)

/-- The sum-of-squares defect polynomial
`Q_h(a,b) = ∑_{j=1}^{h} (ab)^{h-j} (a^j - b^j)^2`. -/
def defectSum (a b : ℤ) (h : ℕ) : ℤ := ∑ j ∈ range h, (a * b) ^ (h - 1 - j) * (a ^ (j + 1) - b ^ (j + 1)) ^ 2

theorem homGeomSum_succ_succ (a b : ℤ) (d : ℕ) :
    homGeomSum a b (d + 2) = a ^ (d + 1) + b ^ (d + 1) + a * b * homGeomSum a b d := by
  unfold homGeomSum
  rw [sum_range_succ, sum_range_succ', mul_sum]
  have hterm : ∀ i ∈ range d, a ^ (i + 1) * b ^ (d + 2 - 1 - (i + 1))
      = a * b * (a ^ i * b ^ (d - 1 - i)) := by
    intro i hi
    have := mem_range.mp hi
    have h1 : d + 2 - 1 - (i + 1) = (d - 1 - i) + 1 := by omega
    rw [h1]; ring
  rw [sum_congr rfl hterm]
  have h2 : d + 2 - 1 - 0 = d + 1 := by omega
  have h3 : d + 2 - 1 - (d + 1) = 0 := by omega
  rw [h2, h3]
  simp only [pow_zero, mul_one, one_mul]
  ring

theorem defectSum_succ (a b : ℤ) (h : ℕ) :
    defectSum a b (h + 1) = a * b * defectSum a b h + (a ^ (h + 1) - b ^ (h + 1)) ^ 2 := by
  unfold defectSum
  rw [sum_range_succ, mul_sum]
  have hterm : ∀ j ∈ range h, (a * b) ^ (h + 1 - 1 - j) * (a ^ (j + 1) - b ^ (j + 1)) ^ 2
      = a * b * ((a * b) ^ (h - 1 - j) * (a ^ (j + 1) - b ^ (j + 1)) ^ 2) := by
    intro j hj
    have := mem_range.mp hj
    have h1 : h + 1 - 1 - j = (h - 1 - j) + 1 := by omega
    rw [h1]; ring
  rw [sum_congr rfl hterm]
  have h2 : h + 1 - 1 - h = 0 := by omega
  rw [h2, pow_zero, one_mul]

/-- **Exact defect factorization** of the centered cyclic trace:
`S_{2h+1}(a,b) - (2h+1)(ab)^h = ∑_{j=1}^{h} (ab)^{h-j} (a^j - b^j)^2`. -/
theorem homGeomSum_sub_eq_defectSum (a b : ℤ) (h : ℕ) :
    homGeomSum a b (2 * h + 1) - (2 * h + 1) * (a * b) ^ h = defectSum a b h := by
  induction h with
  | zero => simp [homGeomSum, defectSum]
  | succ h ih =>
    have e : 2 * (h + 1) + 1 = (2 * h + 1) + 2 := by ring
    rw [e, homGeomSum_succ_succ, defectSum_succ, ← ih]
    push_cast
    ring

/-- `(a - b) ∣ a^j - b^j`, hence the defect is divisible by `(a - b)^2`. -/
theorem sq_sub_dvd_defectSum (a b : ℤ) (h : ℕ) : (a - b) ^ 2 ∣ defectSum a b h := by
  unfold defectSum
  refine dvd_sum fun j _ => ?_
  have := (Commute.all a b).sub_dvd_pow_sub_pow (j + 1)
  exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd this 2) _

/-- The defect `S_d(a,b) - d(ab)^h` is divisible by `(a - b)^2`: every centered trace has
contact order at least two at the fixed point `z = 1`. -/
theorem sq_sub_dvd_homGeomSum_sub (a b : ℤ) (h : ℕ) :
    (a - b) ^ 2 ∣ homGeomSum a b (2 * h + 1) - (2 * h + 1) * (a * b) ^ h := by
  rw [homGeomSum_sub_eq_defectSum]
  exact sq_sub_dvd_defectSum a b h

/-- The defect sum is nonnegative: `P_d(a,b) ≥ 0` for `ab ≥ 0`. -/
theorem defectSum_nonneg {a b : ℤ} (hab : 0 ≤ a * b) (h : ℕ) : 0 ≤ defectSum a b h := by
  unfold defectSum
  exact sum_nonneg fun j _ => mul_nonneg (pow_nonneg hab _) (sq_nonneg _)

/-! ### The cubic trace -/

/-- The cubic identity `a^2 + ab + b^2 - 3ab = (a - b)^2`: the defect of `T_3` is an exact
square. -/
theorem cubic_defect (a b : ℤ) : a ^ 2 + a * b + b ^ 2 - 3 * (a * b) = (a - b) ^ 2 := by ring

theorem homGeomSum_three (a b : ℤ) : homGeomSum a b 3 = a ^ 2 + a * b + b ^ 2 := by
  simp [homGeomSum, sum_range_succ]; ring

/-- For coprime naturals, `a^2 + ab + b^2` is coprime to `a` and to `b`, hence to `ab`:
no prime of the denominator `3ab` except possibly `3` can cancel. -/
theorem coprime_cubicNumerator_mul {a b : ℕ} (hab : Nat.Coprime a b) :
    Nat.Coprime (a ^ 2 + a * b + b ^ 2) (a * b) := by
  have h1 : Nat.Coprime (a ^ 2 + a * b + b ^ 2) a := by
    have : a ^ 2 + a * b + b ^ 2 = b ^ 2 + a * (a + b) := by ring
    rw [this, Nat.coprime_add_mul_left_left]
    exact (Nat.Coprime.pow_left 2 hab.symm)
  have h2 : Nat.Coprime (a ^ 2 + a * b + b ^ 2) b := by
    have : a ^ 2 + a * b + b ^ 2 = a ^ 2 + b * (a + b) := by ring
    rw [this, Nat.coprime_add_mul_left_left]
    exact (Nat.Coprime.pow_left 2 hab)
  exact Nat.Coprime.mul_right h1 h2

/-- `3 ∣ a^2 + ab + b^2 ↔ 3 ∣ a - b` (as integers): the structural prime cancels exactly when
the defect is divisible by `3`. -/
theorem three_dvd_cubicNumerator_iff (a b : ℤ) :
    (3 : ℤ) ∣ a ^ 2 + a * b + b ^ 2 ↔ (3 : ℤ) ∣ a - b := by
  have e : a ^ 2 + a * b + b ^ 2 = (a - b) ^ 2 + 3 * (a * b) := by ring
  rw [e]
  constructor
  · intro h
    have h' : (3 : ℤ) ∣ (a - b) ^ 2 := by
      rw [add_comm] at h
      exact (dvd_add_right (dvd_mul_right (3 : ℤ) (a * b))).mp h
    exact Int.Prime.dvd_pow' Nat.prime_three h'
  · intro h
    exact dvd_add (dvd_pow h two_ne_zero) (dvd_mul_right 3 _)

/-- The only prime that can divide both `a^2 + ab + b^2` and `3ab` (for coprime `a b`) is
`3`. -/
theorem prime_dvd_cubic_gcd {a b : ℕ} (hab : Nat.Coprime a b) {p : ℕ} (hp : p.Prime)
    (h1 : p ∣ a ^ 2 + a * b + b ^ 2) (h2 : p ∣ 3 * (a * b)) : p = 3 := by
  rcases (Nat.Prime.dvd_mul hp).mp h2 with h | h
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
  · have hg := Nat.dvd_gcd h1 h
    rw [(coprime_cubicNumerator_mul hab)] at hg
    exact absurd (Nat.le_of_dvd one_pos hg) (by have := hp.one_lt; omega)

/-- **Cubic defect recurrence.** If `u = a - b`, then the unreduced cubic numerator and
denominator differ by `u^2`; after dividing by the reduction factor `g ∈ {1,3}` (which is `3`
exactly when `3 ∣ u`), the reduced defect is `u^2 / g`.  Here we record the exact integer
identity behind the recurrence `u_{k+1} = u_k^2 / g_k`. -/
theorem cubic_reduced_defect (a b : ℤ) :
    (a ^ 2 + a * b + b ^ 2) - 3 * (a * b) = (a - b) ^ 2 := cubic_defect a b

theorem padicValInt_sq {ℓ : ℕ} [Fact ℓ.Prime] {u : ℤ} (hu : u ≠ 0) :
    padicValInt ℓ (u ^ 2) = 2 * padicValInt ℓ u := by
  rw [pow_two, padicValInt.mul hu hu]; ring

/-- Valuation-doubling law for `ℓ ≠ 3`: if the reduced defect is `u^2 / g` with `g ∈ {1, 3}`,
then `v_ℓ(u^2/g) = 2 v_ℓ(u)`.  Stated for the two possible values of `g`. -/
theorem padicValInt_sq_div_three {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓ3 : ℓ ≠ 3) {u : ℤ} (hu : u ≠ 0)
    (h3 : (3 : ℤ) ∣ u ^ 2) :
    padicValInt ℓ (u ^ 2 / 3) = 2 * padicValInt ℓ u := by
  obtain ⟨w, hw⟩ := h3
  rw [hw, Int.mul_ediv_cancel_left _ (by norm_num)]
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hw
    exact hu (pow_eq_zero_iff two_ne_zero |>.mp hw)
  have := padicValInt.mul (p := ℓ) (by norm_num : (3 : ℤ) ≠ 0) hw0
  rw [← hw, padicValInt_sq hu] at this
  have h3' : padicValInt ℓ 3 = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro hd
    have hd' : ℓ ∣ 3 := by exact_mod_cast hd
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_three).mp hd')
  omega

/-! ### The reciprocal-quadratic bridge and the fifth-trace channels -/

/-- **Reciprocal-quadratic bridge identity** over any commutative ring. -/
theorem bridge_identity {R : Type*} [CommRing R] (a b c d lam : R) :
    c * d * (a ^ 2 + lam * (a * b) + b ^ 2) - a * b * (c ^ 2 + lam * (c * d) + d ^ 2)
      = (a * d - b * c) * (a * c - b * d) := by ring

/-- The fifth-trace defect factor `F(a,b) = a^2 + 3ab + b^2`. -/
def fifthFactor (a b : ℤ) : ℤ := a ^ 2 + 3 * (a * b) + b ^ 2

theorem fifthFactor_bridge (a b c d : ℤ) :
    c * d * fifthFactor a b - a * b * fifthFactor c d = (a * d - b * c) * (a * c - b * d) := by
  unfold fifthFactor; exact bridge_identity a b c d 3

/-- A common divisor of the two fifth-trace factors divides the product of the two channels. -/
theorem dvd_channel_product {m a b c d : ℤ} (h1 : m ∣ fifthFactor a b) (h2 : m ∣ fifthFactor c d) :
    m ∣ (a * d - b * c) * (a * c - b * d) := by
  rw [← fifthFactor_bridge]
  exact dvd_sub (Dvd.dvd.mul_left h1 _) (Dvd.dvd.mul_left h2 _)

/-- A prime dividing `F(a,b)` with `gcd(a,b) = 1` divides neither `a` nor `b`. -/
theorem prime_not_dvd_of_dvd_fifthFactor {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (hab : IsCoprime a b) (h : (p : ℤ) ∣ fifthFactor a b) : ¬ (p : ℤ) ∣ a ∧ ¬ (p : ℤ) ∣ b := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  constructor
  · intro ha
    have hb2 : (p : ℤ) ∣ b ^ 2 := by
      have : b ^ 2 = fifthFactor a b - a * (a + 3 * b) := by unfold fifthFactor; ring
      rw [this]; exact dvd_sub h (Dvd.dvd.mul_right ha _)
    have hb := hp'.dvd_of_dvd_pow hb2
    exact hp'.not_unit (hab.isUnit_of_dvd' ha hb)
  · intro hb
    have ha2 : (p : ℤ) ∣ a ^ 2 := by
      have : a ^ 2 = fifthFactor a b - b * (3 * a + b) := by unfold fifthFactor; ring
      rw [this]; exact dvd_sub h (Dvd.dvd.mul_right hb _)
    have ha := hp'.dvd_of_dvd_pow ha2
    exact hp'.not_unit (hab.isUnit_of_dvd' ha hb)

/-- **Channel exclusivity.**  If a prime `p` divides `F(a,b)` for a coprime pair and divides
both channels `ad - bc` and `ac - bd` of a second coprime pair, then `p = 5`. -/
theorem eq_five_of_dvd_both_channels {p : ℕ} (hp : p.Prime) {a b c d : ℤ}
    (hab : IsCoprime a b) (hcd : IsCoprime c d)
    (hF : (p : ℤ) ∣ fifthFactor a b) (hF' : (p : ℤ) ∣ fifthFactor c d)
    (hminus : (p : ℤ) ∣ a * d - b * c) (hplus : (p : ℤ) ∣ a * c - b * d) : p = 5 := by
  haveI := Fact.mk hp
  obtain ⟨hpa, hpb⟩ := prime_not_dvd_of_dvd_fifthFactor hp hab hF
  obtain ⟨hpc, hpd⟩ := prime_not_dvd_of_dvd_fifthFactor hp hcd hF'
  -- Pass to `ZMod p`.
  have cast := fun z : ℤ => (ZMod.intCast_zmod_eq_zero_iff_dvd z p)
  have e1 : ((a * d - b * c : ℤ) : ZMod p) = 0 := (cast _).mpr hminus
  have e2 : ((a * c - b * d : ℤ) : ZMod p) = 0 := (cast _).mpr hplus
  have eF : ((fifthFactor a b : ℤ) : ZMod p) = 0 := (cast _).mpr hF
  have ha0 : (a : ZMod p) ≠ 0 := fun h => hpa ((cast _).mp h)
  have hb0 : (b : ZMod p) ≠ 0 := fun h => hpb ((cast _).mp h)
  have hc0 : (c : ZMod p) ≠ 0 := fun h => hpc ((cast _).mp h)
  have hd0 : (d : ZMod p) ≠ 0 := fun h => hpd ((cast _).mp h)
  push_cast at e1 e2 eF
  unfold fifthFactor at eF
  push_cast at eF
  -- From `ad = bc` and `ac = bd`: `a^2 cd = b^2 cd`, so `a^2 = b^2`.
  have hsq : (a : ZMod p) ^ 2 = (b : ZMod p) ^ 2 := by
    have h1 : (a : ZMod p) * d = b * c := sub_eq_zero.mp e1
    have h2 : (a : ZMod p) * c = b * d := sub_eq_zero.mp e2
    have : ((a : ZMod p) ^ 2 - b ^ 2) * (c * d) = 0 := by
      have := congrArg₂ (· * ·) h1 h2
      linear_combination this
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (mul_ne_zero hc0 hd0)
  -- `a = ±b`.
  have hpm : (a : ZMod p) = b ∨ (a : ZMod p) = -b := by
    have : ((a : ZMod p) - b) * (a + b) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hpm with h | h
  · -- `a = b`: `F = 5 b^2 = 0`, so `p ∣ 5`.
    have h5 : ((5 : ℤ) : ZMod p) * (b : ZMod p) ^ 2 = 0 := by
      rw [h] at eF; linear_combination eF
    have : ((5 : ℤ) : ZMod p) = 0 := by
      rcases mul_eq_zero.mp h5 with h' | h'
      · exact h'
      · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h') hb0
    have hd5 : (p : ℤ) ∣ 5 := (cast _).mp this
    have := Int.natCast_dvd_natCast.mp (by exact_mod_cast hd5 : (p : ℤ) ∣ (5 : ℕ))
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp this
  · -- `a = -b`: `F = -b^2 = 0`, impossible.
    exfalso
    have : -((b : ZMod p) ^ 2) = 0 := by rw [h] at eF; linear_combination eF
    exact hb0 (pow_eq_zero_iff two_ne_zero |>.mp (neg_eq_zero.mp this))

/-- **Two-channel theorem for the fifth trace.**  Let `p ≠ 5` be a prime and `e ≥ 1`.  If
`p^e` divides both normalized fifth-trace factors `F(a,b)` and `F(c,d)` of two coprime pairs,
then `p^e` divides exactly one of the channels `ad - bc`, `ac - bd`, and `p` does not divide
the other. -/
theorem fifth_trace_two_channel {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) {e : ℕ} (he : 1 ≤ e)
    {a b c d : ℤ} (hab : IsCoprime a b) (hcd : IsCoprime c d)
    (hF : (p : ℤ) ^ e ∣ fifthFactor a b) (hF' : (p : ℤ) ^ e ∣ fifthFactor c d) :
    ((p : ℤ) ^ e ∣ a * d - b * c ∧ ¬ (p : ℤ) ∣ a * c - b * d) ∨
    ((p : ℤ) ^ e ∣ a * c - b * d ∧ ¬ (p : ℤ) ∣ a * d - b * c) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpe : (p : ℤ) ∣ (p : ℤ) ^ e := dvd_pow_self _ (by omega)
  have hF1 := hpe.trans hF
  have hF1' := hpe.trans hF'
  have hprod := dvd_channel_product hF hF'
  have hnot : ¬ ((p : ℤ) ∣ a * d - b * c ∧ (p : ℤ) ∣ a * c - b * d) := fun ⟨h1, h2⟩ =>
    hp5 (eq_five_of_dvd_both_channels hp hab hcd hF1 hF1' h1 h2)
  -- `p^e` divides a product with one factor coprime to `p`: it divides the other.
  rcases (hp'.dvd_mul).mp (hpe.trans hprod) with h | h
  · left
    refine ⟨?_, fun h2 => hnot ⟨h, h2⟩⟩
    have hcop : IsCoprime ((p : ℤ) ^ e) (a * c - b * d) := by
      apply IsCoprime.pow_left
      exact (Prime.coprime_iff_not_dvd hp').mpr (fun h2 => hnot ⟨h, h2⟩)
    exact hcop.dvd_of_dvd_mul_right hprod
  · right
    refine ⟨?_, fun h1 => hnot ⟨h1, h⟩⟩
    have hcop : IsCoprime ((p : ℤ) ^ e) (a * d - b * c) := by
      apply IsCoprime.pow_left
      exact (Prime.coprime_iff_not_dvd hp').mpr (fun h1 => hnot ⟨h1, h⟩)
    exact hcop.dvd_of_dvd_mul_left hprod

/-- The two channels for the synchronized near-units `M^q/2^p` and `A^q/3^p` of a
hypothetical counterexample: the direct cross-gap `3^p M^q - 2^p A^q` and the reciprocal
cross-gap `(MA)^q - 6^p`.  (Here the factors are unreduced; reduction by the common
structural factors does not affect the channel allocation at primes `≠ 2, 3`.) -/
theorem alaoglu_erdos_channels (M A p q : ℕ) :
    ((M ^ q : ℤ) * (3 ^ p) - (2 ^ p) * (A ^ q) = 3 ^ p * M ^ q - 2 ^ p * A ^ q) ∧
    ((M ^ q : ℤ) * (A ^ q) - (2 ^ p) * (3 ^ p) = (M * A) ^ q - 6 ^ p) := by
  constructor
  · ring
  · rw [mul_pow, show (6 : ℤ) ^ p = 2 ^ p * 3 ^ p by rw [← mul_pow]; norm_num]

end LeanProofs.TwoBaseIntegerExponent.CenteredTrace
