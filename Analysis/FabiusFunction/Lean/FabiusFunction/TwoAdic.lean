import FabiusFunction.NormalizedEvenMoments
import FabiusFunction.Parity
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Two-adic parity of the half moments

This file proves the exact numerator and denominator parity asserted in
Theorem 20 of Arias de Reyna's *Arithmetic of the Fabius function*.  The odd
indices reduce to the normalized even moments.  At an even index, the
recurrence for `halfMoment` reduces parity to the number of odd entries in an
odd-indexed row of Pascal's triangle, supplied by `FabiusFunction.Parity`.

The final section converts the parity result into the dyadic valuation of the
Fabius value at `2⁻ⁿ`, the valuation component of Theorem 21.  Parameter-free
forms isolate the exceptional zeroth half moment, and Legendre's formula at
`p = 2` removes the remaining factorial valuation in favor of binary weight.
Kummer's theorem identifies the binary-weight loss under arbitrary addition
with the two-adic valuation of one binomial coefficient.  This gives a
carry-twisted multiplication law for the Thue--Morse sign and, on the diagonal,
the central-binomial formula.
-/

set_option autoImplicit false

open scoped BigOperators Interval
open Finset

namespace Fabius

private lemma odd_num_mul_iff {q r : ℚ} (hq : Odd q.den) (hr : Odd r.den) :
    Odd (q * r).num ↔ Odd q.num ∧ Odd r.num := by
  have hprod := Rat.mul_num_den' q r
  have hq' : Odd (q.den : ℤ) := by exact_mod_cast hq
  have hr' : Odd (r.den : ℤ) := by exact_mod_cast hr
  have hqr' : Odd ((q * r).den : ℤ) := by
    exact_mod_cast rat_den_mul_odd hq hr
  have hparity :
      Odd ((q * r).num * q.den * r.den) ↔
        Odd (q.num * r.num * (q * r).den) := by
    rw [hprod]
  simpa only [Int.odd_mul, hq', hr', hqr', and_true] using hparity

private lemma odd_num_add_iff {q r : ℚ} (hq : Odd q.den) (hr : Odd r.den) :
    Odd (q + r).num ↔ (Odd q.num ↔ Even r.num) := by
  have hadd := Rat.add_num_den' q r
  have hq' : Odd (q.den : ℤ) := by exact_mod_cast hq
  have hr' : Odd (r.den : ℤ) := by exact_mod_cast hr
  have hnq' : ¬ Even (q.den : ℤ) := Int.not_even_iff_odd.mpr hq'
  have hsum' : Odd ((q + r).den : ℤ) := by
    exact_mod_cast rat_den_add_odd hq hr
  have hparity :
      Odd ((q + r).num * q.den * r.den) ↔
        Odd ((q.num * r.den + r.num * q.den) * (q + r).den) := by
    rw [hadd]
  simp only [Int.odd_mul, Int.odd_add, Int.even_mul, hq', hr', hnq', hsum',
    and_true, or_false] at hparity
  exact hparity

private lemma odd_den_sum_and_odd_num_iff_card {alpha : Type*}
    [DecidableEq alpha] (s : Finset alpha) (f : alpha → ℚ)
    (hden : ∀ x ∈ s, Odd (f x).den) :
    Odd (∑ x ∈ s, f x).den ∧
      (Odd (∑ x ∈ s, f x).num ↔
        Odd (s.filter (fun x => Odd (f x).num)).card) := by
  induction s using Finset.induction_on with
  | empty => norm_num
  | @insert a s ha ih =>
      have hfa : Odd (f a).den := hden a (mem_insert_self a s)
      have hrest : ∀ x ∈ s, Odd (f x).den := by
        intro x hx
        exact hden x (mem_insert_of_mem hx)
      have hi := ih hrest
      rw [sum_insert ha]
      constructor
      · exact rat_den_add_odd hfa hi.1
      · rw [odd_num_add_iff hfa hi.1]
        by_cases hodd : Odd (f a).num
        · have hanot : a ∉ s.filter (fun x => Odd (f x).num) :=
            fun h => ha (mem_of_mem_filter a h)
          simp only [hodd, true_iff, Finset.filter_insert, if_true,
            Finset.card_insert_of_notMem hanot]
          calc
            Even (∑ x ∈ s, f x).num ↔ ¬ Odd (∑ x ∈ s, f x).num :=
              Int.not_odd_iff_even.symm
            _ ↔ ¬ Odd (s.filter (fun x => Odd (f x).num)).card :=
              not_congr hi.2
            _ ↔ Even (s.filter (fun x => Odd (f x).num)).card :=
              Nat.not_odd_iff_even
            _ ↔ Odd ((s.filter (fun x => Odd (f x).num)).card + 1) := by
              constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by omega⟩
        · simp [Finset.filter_insert, hodd, hi.2]

private lemma odd_num_den_of_eq_divInt {q : ℚ} {a d : ℤ}
    (hq : q = Rat.divInt a d) (ha : Odd a) (hd : Odd d) :
    Odd q.num.natAbs ∧ Odd q.den := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    norm_num at hd
  obtain ⟨c, hnum, hden⟩ := Rat.num_den_mk hd0 hq
  have hdenProd : Odd (c * (q.den : ℤ)) := by rwa [← hden]
  have hnumProd : Odd (c * q.num) := by rwa [← hnum]
  have hqdenInt : Odd (q.den : ℤ) := (Int.odd_mul.mp hdenProd).2
  have hqnum : Odd q.num := (Int.odd_mul.mp hnumProd).2
  constructor
  · exact Int.natAbs_odd.mpr hqnum
  · exact_mod_cast hqdenInt

private lemma odd_num_den_of_eq_nat_div {q : ℚ} {a d : ℕ}
    (hq : q = (a : ℚ) / d) (ha : Odd a) (hd : Odd d) :
    Odd q.num.natAbs ∧ Odd q.den := by
  apply odd_num_den_of_eq_divInt (a := (a : ℤ)) (d := (d : ℤ))
  · simpa [Rat.divInt_eq_div] using hq
  · exact_mod_cast ha
  · exact_mod_cast hd

/-- Both the reduced numerator and denominator of every even moment are odd. -/
theorem moment_num_den_odd (n : ℕ) :
    Odd (moment n).num.natAbs ∧ Odd (moment n).den := by
  rw [moment_eq_momentNumerator_div]
  apply odd_num_den_of_eq_nat_div
  · rfl
  · exact momentNumerator_odd n
  · exact (odd_oddDoubleFactorial (n + 1)).mul
      (odd_evenMersenneProduct n)

private lemma nat_mul_odd_den_and_num_iff (a : ℕ) {q : ℚ}
    (hqden : Odd q.den) :
    Odd (((a : ℚ) * q).den) ∧
      (Odd (((a : ℚ) * q).num) ↔ Odd a ∧ Odd q.num) := by
  constructor
  · exact rat_den_mul_odd (by simp) hqden
  · simpa using odd_num_mul_iff (q := (a : ℚ)) (r := q) (by simp) hqden

private lemma two_mul_halfMoment_odd_index_num_den (n : ℕ) :
    Odd (2 * halfMoment (2 * n + 1)).num.natAbs ∧
      Odd (2 * halfMoment (2 * n + 1)).den := by
  have heq :
      2 * halfMoment (2 * n + 1) = ((2 * n + 1 : ℕ) : ℚ) * moment n := by
    rw [halfMoment_odd_eq_moment]
    ring
  rw [heq]
  have hm := moment_num_den_odd n
  have hmnum : Odd (moment n).num := Int.natAbs_odd.mp hm.1
  have hmul := nat_mul_odd_den_and_num_iff (2 * n + 1) hm.2
  constructor
  · apply Int.natAbs_odd.mpr
    exact hmul.2.2 ⟨odd_two_mul_add_one n, hmnum⟩
  · exact hmul.1

/-- All-index form of equation (31) of *Arithmetic of the Fabius function*:
the isolated half-moment recurrence after multiplying every term by two.
At `N = 0`, both sides are zero. -/
theorem two_mul_halfMoment_recurrence_all (N : ℕ) :
    ((((N + 1) * (2 ^ N - 1) : ℕ) : ℚ) * (2 * halfMoment N)) =
      ∑ k : Fin N,
        (Nat.choose (N + 1) k.val : ℚ) * (2 * halfMoment k.val) := by
  by_cases hN : N = 0
  · subst N
    norm_num
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le
    (Nat.one_le_iff_ne_zero.mpr hN)
  rw [show 1 + m = m + 1 by omega, halfMoment_succ]
  have hpow : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  push_cast [Nat.cast_sub hpow]
  rw [show (∑ k : Fin (m + 1),
        (Nat.choose (m + 2) k.val : ℚ) * (2 * halfMoment k.val)) =
      2 * ∑ k : Fin (m + 1),
        (Nat.choose (m + 2) k.val : ℚ) * halfMoment k.val by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring]
  rw [show (m : ℚ) + 1 + 1 = (m : ℚ) + 2 by ring]
  let D : ℚ := ((m : ℚ) + 2) * ((2 : ℚ) ^ (m + 1) - 1)
  let S : ℚ := ∑ k : Fin (m + 1),
    (Nat.choose (m + 2) k.val : ℚ) * halfMoment k.val
  change D * (2 * (S / D)) = 2 * S
  have hD : D ≠ 0 := by
    dsimp [D]
    apply mul_ne_zero
    · positivity
    · exact sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ (by norm_num) (by omega)))
  field_simp [hD]

/-- Positive-index form of equation (31), retained with its original
signature for source compatibility. -/
theorem two_mul_halfMoment_recurrence (N : ℕ) (hN : 1 ≤ N) :
    ((((N + 1) * (2 ^ N - 1) : ℕ) : ℚ) * (2 * halfMoment N)) =
      ∑ k : Fin N,
        (Nat.choose (N + 1) k.val : ℚ) * (2 * halfMoment k.val) := by
  have _hN0 : N ≠ 0 := Nat.one_le_iff_ne_zero.mp hN
  exact two_mul_halfMoment_recurrence_all N

private lemma odd_inner_binomial_count (m : ℕ) (hm : 1 ≤ m) :
    Odd (((range (2 * m)).filter (fun k =>
      k ≠ 0 ∧ Odd (Nat.choose (2 * m + 1) k))).card) := by
  rw [card_odd_inner_binomial_coefficients m hm]
  have hpowEven : Even (2 ^ (binaryWeight m + 1)) := by
    rw [pow_succ]
    exact even_two.mul_left _
  have hcardPos : 0 < ((range (2 * m)).filter (fun k =>
      k ≠ 0 ∧ Odd (Nat.choose (2 * m + 1) k))).card := by
    apply Finset.card_pos.mpr
    refine ⟨1, ?_⟩
    simp only [mem_filter, mem_range, Nat.choose_one_right]
    exact ⟨by omega, by norm_num, odd_two_mul_add_one m⟩
  rw [card_odd_inner_binomial_coefficients m hm] at hcardPos
  exact Nat.Even.sub_odd (by omega) hpowEven (by decide)

/-- For a positive index, both reduced numerator and denominator of
`2 * halfMoment n` are odd. -/
theorem two_mul_halfMoment_num_den_odd (n : ℕ) (hn : 0 < n) :
    Odd (2 * halfMoment n).num.natAbs ∧ Odd (2 * halfMoment n).den := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have hm : 1 ≤ m := by omega
      let term : Fin (2 * m) → ℚ := fun k =>
        (Nat.choose (2 * m + 1) k.val : ℚ) * (2 * halfMoment k.val)
      let S : ℚ := ∑ k : Fin (2 * m), term k
      have htermDen (k : Fin (2 * m)) : Odd (term k).den := by
        by_cases hk0 : k.val = 0
        · norm_num [term, hk0, halfMoment]
        · have hk := ih k.val k.isLt (Nat.pos_of_ne_zero hk0)
          exact (nat_mul_odd_den_and_num_iff
            (Nat.choose (2 * m + 1) k.val) hk.2).1
      have htermNum (k : Fin (2 * m)) :
          Odd (term k).num ↔
            k.val ≠ 0 ∧ Odd (Nat.choose (2 * m + 1) k.val) := by
        by_cases hk0 : k.val = 0
        · norm_num [term, hk0, halfMoment]
        · have hk := ih k.val k.isLt (Nat.pos_of_ne_zero hk0)
          have hknum : Odd (2 * halfMoment k.val).num := Int.natAbs_odd.mp hk.1
          have hmul := (nat_mul_odd_den_and_num_iff
            (Nat.choose (2 * m + 1) k.val) hk.2).2
          simpa [term, hk0, hknum] using hmul
      have hsum := odd_den_sum_and_odd_num_iff_card
        (Finset.univ : Finset (Fin (2 * m))) term (by
          intro k hk
          exact htermDen k)
      simp_rw [htermNum] at hsum
      have hcount :
          Odd (((Finset.univ : Finset (Fin (2 * m))).filter (fun k =>
            k.val ≠ 0 ∧ Odd (Nat.choose (2 * m + 1) k.val))).card) := by
        let p : ℕ → Prop := fun k =>
          k ≠ 0 ∧ Odd (Nat.choose (2 * m + 1) k)
        have hcard := card_filter_fin_eq_range (2 * m) p
        have hrange : Odd (((range (2 * m)).filter p).card) := by
          simpa only [p] using odd_inner_binomial_count m hm
        exact hcard.symm ▸ hrange
      have hSden : Odd S.den := hsum.1
      have hSnum : Odd S.num.natAbs := by
        exact Int.natAbs_odd.mpr (hsum.2.mpr hcount)
      let A : ℕ := (2 * m + 1) * (2 ^ (2 * m) - 1)
      have hAodd : Odd A := by
        exact (odd_two_mul_add_one m).mul
          (two_pow_sub_one_odd (by omega))
      have hA0 : A ≠ 0 := Nat.ne_of_gt hAodd.pos
      have hrec := two_mul_halfMoment_recurrence_all (2 * m)
      change (A : ℚ) * (2 * halfMoment (2 * m)) = S at hrec
      have hquot : 2 * halfMoment (2 * m) = S / (A : ℚ) := by
        apply (eq_div_iff (by exact_mod_cast hA0)).2
        simpa [mul_comm] using hrec
      have hrepr :
          2 * halfMoment (2 * m) =
            Rat.divInt S.num ((S.den * A : ℕ) : ℤ) := by
        calc
          2 * halfMoment (2 * m) = S / (A : ℚ) := hquot
          _ = Rat.divInt S.num ((S.den * A : ℕ) : ℤ) := by
            nth_rw 1 [← Rat.num_div_den S]
            simp only [Rat.divInt_eq_div]
            push_cast
            field_simp [hA0, S.den_ne_zero]
      apply odd_num_den_of_eq_divInt (d := ((S.den * A : ℕ) : ℤ))
      · exact hrepr
      · exact Int.natAbs_odd.mp hSnum
      · exact_mod_cast hSden.mul hAodd
    · exact two_mul_halfMoment_odd_index_num_den m

private lemma padicValRat_two_eq_zero_of_odd_num_den {q : ℚ}
    (hnum : Odd q.num.natAbs) (hden : Odd q.den) :
    padicValRat 2 q = 0 := by
  rw [padicValRat_def]
  unfold padicValInt
  rw [padicValNat.eq_zero_of_not_dvd hnum.not_two_dvd_nat,
    padicValNat.eq_zero_of_not_dvd hden.not_two_dvd_nat]
  norm_num

/-- Every even moment is a two-adic unit. -/
theorem moment_padicVal_two (n : ℕ) : padicValRat 2 (moment n) = 0 := by
  have hodd := moment_num_den_odd n
  exact padicValRat_two_eq_zero_of_odd_num_den hodd.1 hodd.2

/-- Theorem 20's exact-arithmetic content: `2 * halfMoment n` is a two-adic
unit, witnessed by its odd reduced numerator and denominator. -/
theorem two_mul_halfMoment_padicVal_two_and_odd (n : ℕ) (hn : 1 ≤ n) :
    padicValRat 2 (2 * halfMoment n) = 0 ∧
      Odd (2 * halfMoment n).num.natAbs ∧
      Odd (2 * halfMoment n).den := by
  have hodd := two_mul_halfMoment_num_den_odd n (by omega)
  exact ⟨padicValRat_two_eq_zero_of_odd_num_den hodd.1 hodd.2, hodd⟩

/-- The reduced numerator of `2 * halfMoment n` is odd exactly at the
positive indices.  This packages the exceptional value at `n = 0` into a
parameter-free characterization. -/
theorem two_mul_halfMoment_num_odd_iff_pos (n : ℕ) :
    Odd (2 * halfMoment n).num.natAbs ↔ 0 < n := by
  constructor
  · intro hodd
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    norm_num [halfMoment] at hodd
    exact (Nat.not_odd_iff_even.mpr even_two) hodd
  · intro hn
    exact (two_mul_halfMoment_num_den_odd n hn).1

/-- Every positive-index half moment has two-adic valuation `-1`. -/
theorem halfMoment_padicVal_two (n : ℕ) (hn : 0 < n) :
    padicValRat 2 (halfMoment n) = -1 := by
  have htwenty := two_mul_halfMoment_padicVal_two_and_odd n (by omega)
  have hhalfMomentNe : halfMoment n ≠ 0 := ne_of_gt (halfMoment_pos n)
  have hvalTwo : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 2) (by omega)
  have hmul := padicValRat.mul (p := 2) (q := (2 : ℚ))
    (r := halfMoment n) (by norm_num) hhalfMomentNe
  rw [hvalTwo, htwenty.1] at hmul
  omega

/-- Parameter-free two-adic valuation of the half-moment sequence, including
the exceptional zeroth value. -/
theorem halfMoment_padicVal_two_eq_ite (n : ℕ) :
    padicValRat 2 (halfMoment n) = if n = 0 then 0 else -1 := by
  by_cases hn : n = 0
  · subst n
    norm_num [halfMoment]
  · rw [if_neg hn]
    exact halfMoment_padicVal_two n (Nat.pos_of_ne_zero hn)

/-- Multiplication preserves oddness of both reduced numerators and
denominators. -/
theorem odd_num_den_mul {q r : ℚ}
    (hq : Odd q.num.natAbs ∧ Odd q.den)
    (hr : Odd r.num.natAbs ∧ Odd r.den) :
    Odd (q * r).num.natAbs ∧ Odd (q * r).den := by
  constructor
  · apply Int.natAbs_odd.mpr
    exact (odd_num_mul_iff hq.2 hr.2).2
      ⟨Int.natAbs_odd.mp hq.1, Int.natAbs_odd.mp hr.1⟩
  · exact rat_den_mul_odd hq.2 hr.2

/-- Multiplication by an odd natural preserves oddness of the reduced
numerator and denominator of a rational. -/
theorem odd_num_den_mul_nat {q : ℚ} (a : ℕ)
    (hq : Odd q.num.natAbs ∧ Odd q.den) (ha : Odd a) :
    Odd (q * (a : ℚ)).num.natAbs ∧ Odd (q * (a : ℚ)).den := by
  rw [mul_comm]
  have hmul := nat_mul_odd_den_and_num_iff a hq.2
  constructor
  · apply Int.natAbs_odd.mpr
    exact hmul.2.2 ⟨ha, Int.natAbs_odd.mp hq.1⟩
  · exact hmul.1

/-- A natural rational with odd reduced numerator is an odd natural. -/
theorem isOddNatural_of_isNatural_of_odd_num {q : ℚ}
    (hnat : IsNatural q) (hodd : Odd q.num.natAbs) : IsOddNatural q := by
  rcases hnat with ⟨m, rfl⟩
  refine ⟨m, ?_, rfl⟩
  simpa using hodd

/-- An odd divisor of a power of two is one. -/
theorem odd_eq_one_of_dvd_two_pow {d e : ℕ} (hd : Odd d)
    (hdvd : d ∣ 2 ^ e) : d = 1 := by
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    have heven : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, hk0⟩
    exact (Nat.not_even_iff_odd.mpr hd) heven
  simp [hk0]

/-- A nonnegative rational with reduced denominator one is natural. -/
theorem isNatural_of_den_eq_one_of_nonneg {q : ℚ} (hden : q.den = 1)
    (hq : 0 ≤ q) : IsNatural q := by
  refine ⟨q.num.natAbs, ?_⟩
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  calc
    q = (q.num : ℚ) := (Rat.coe_int_num_of_den_eq_one hden).symm
    _ = (q.num.natAbs : ℕ) := by
      calc
        (q.num : ℚ) = ((q.num.natAbs : ℤ) : ℚ) :=
          congrArg (fun z : ℤ => (z : ℚ)) (Int.natAbs_of_nonneg hnum).symm
        _ = (q.num.natAbs : ℕ) := by norm_num

/-- Legendre's formula at `p = 2`: the valuation of `n!` is `n` minus the
binary digit sum of `n`. -/
theorem factorial_padicVal_two (n : ℕ) :
    padicValRat 2 (n.factorial : ℚ) =
      ((n - binaryWeight n : ℕ) : ℤ) := by
  rw [padicValRat.of_nat]
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  simpa [binaryWeight] using congrArg (fun k : ℕ => (k : ℤ)) h

/-- Kummer's digit-sum formula at two for an arbitrary binomial coefficient. -/
theorem addChoose_padicValNat_two (a b : ℕ) :
    padicValNat 2 (Nat.choose (a + b) a) =
      binaryWeight a + binaryWeight b - binaryWeight (a + b) := by
  rw [add_comm a b]
  simpa [binaryWeight] using
    (sub_one_mul_padicValNat_choose_eq_sub_sum_digits'
      (p := 2) (n := b) (k := a))

private lemma binaryWeight_add_addChoose_padicValNat_two (a b : ℕ) :
    binaryWeight (a + b) +
        padicValNat 2 (Nat.choose (a + b) a) =
      binaryWeight a + binaryWeight b := by
  have hweight_le (n : ℕ) : binaryWeight n ≤ n := by
    simpa [binaryWeight] using Nat.digit_sum_le 2 n
  have hchoose : Nat.choose (a + b) a ≠ 0 :=
    Nat.choose_ne_zero (Nat.le_add_right a b)
  have hfactorialIdentity :
      Nat.choose (a + b) a * a.factorial * b.factorial =
        (a + b).factorial := by
    rw [Nat.choose_symm_add (a := a) (b := b)]
    exact Nat.add_choose_mul_factorial_mul_factorial a b
  have h := congrArg (padicValNat 2) hfactorialIdentity
  rw [padicValNat.mul
        (mul_ne_zero hchoose (Nat.factorial_ne_zero a))
        (Nat.factorial_ne_zero b),
      padicValNat.mul hchoose (Nat.factorial_ne_zero a)] at h
  change padicValNat 2 (Nat.choose (a + b) a) +
          padicValNat 2 a.factorial + padicValNat 2 b.factorial =
        padicValNat 2 (a + b).factorial at h
  have hfactorialNat (n : ℕ) :
      padicValNat 2 n.factorial = n - binaryWeight n := by
    have hn := sub_one_mul_padicValNat_factorial (p := 2) n
    simpa [binaryWeight] using hn
  rw [hfactorialNat a, hfactorialNat b, hfactorialNat (a + b)] at h
  have ha := hweight_le a
  have hb := hweight_le b
  have hab := hweight_le (a + b)
  omega

/-- Ordinary addition is Thue--Morse multiplicative up to the two-adic carry
valuation of its binomial coefficient. -/
theorem thueMorseSign_add_valuation (a b : ℕ) :
    thueMorseSign (a + b) =
      thueMorseSign a * thueMorseSign b *
        (-1 : ℤ) ^ padicValNat 2 (Nat.choose (a + b) a) := by
  let v : ℕ := padicValNat 2 (Nat.choose (a + b) a)
  change thueMorseSign (a + b) =
    thueMorseSign a * thueMorseSign b * (-1 : ℤ) ^ v
  have hbalance :
      binaryWeight (a + b) + v = binaryWeight a + binaryWeight b := by
    simpa only [v] using binaryWeight_add_addChoose_padicValNat_two a b
  simp only [thueMorseSign]
  calc
    (-1 : ℤ) ^ binaryWeight (a + b) =
        (-1 : ℤ) ^ binaryWeight (a + b) * (-1 : ℤ) ^ (v + v) := by
      rw [(Even.add_self v).neg_one_pow, mul_one]
    _ = (-1 : ℤ) ^ ((binaryWeight (a + b) + v) + v) := by
      rw [← pow_add, ← add_assoc]
    _ = (-1 : ℤ) ^ ((binaryWeight a + binaryWeight b) + v) := by
      rw [hbalance]
    _ = (-1 : ℤ) ^ binaryWeight a * (-1 : ℤ) ^ binaryWeight b *
          (-1 : ℤ) ^ v := by
      rw [pow_add, pow_add]

/-- Kummer's theorem at `p = 2`: the two-adic valuation of the central
binomial coefficient is the binary weight. -/
theorem centralChoose_padicValNat_two (n : ℕ) :
    padicValNat 2 (Nat.choose (2 * n) n) = binaryWeight n := by
  have hKummer :=
    sub_one_mul_padicValNat_choose_eq_sub_sum_digits'
      (p := 2) (n := n) (k := n)
  have hdouble :
      (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum := by
    by_cases hn : n = 0
    · simp [hn]
    · rw [Nat.digits_base_mul Nat.one_lt_two (Nat.pos_of_ne_zero hn)]
      simp
  calc
    padicValNat 2 (Nat.choose (2 * n) n) =
        (Nat.digits 2 n).sum + (Nat.digits 2 n).sum -
          (Nat.digits 2 (2 * n)).sum := by
      simpa [two_mul] using hKummer
    _ = binaryWeight n := by
      rw [hdouble]
      simp [binaryWeight]

/-- A single central binomial coefficient recovers the Thue--Morse sign. -/
theorem thueMorseSign_centralChoose (n : ℕ) :
    thueMorseSign n =
      (-1 : ℤ) ^ padicValNat 2 (Nat.choose (2 * n) n) := by
  rw [centralChoose_padicValNat_two, thueMorseSign]

/-- The two-adic valuation of the Fabius value at `2⁻ⁿ`, i.e. the
valuation equality in Theorem 21. -/
theorem fabiusAtInverseTwoPow_padicVal_two (n : ℕ) (hn : 1 ≤ n) :
    padicValRat 2 (fabiusAtInverseTwoPow n) =
      -(n.choose 2 : ℤ) - 1 - padicValRat 2 (n.factorial : ℚ) := by
  have hhalfMomentNe : halfMoment n ≠ 0 := ne_of_gt (halfMoment_pos n)
  have hvalTwo : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 2) (by omega)
  have hhalfMomentVal := halfMoment_padicVal_two n (by omega)
  have hfactorialNe : (n.factorial : ℚ) ≠ 0 := by positivity
  have hpowNe : (2 : ℚ) ^ n.choose 2 ≠ 0 := by positivity
  rw [fabiusAtInverseTwoPow_eq_halfMoment, halfMomentFabiusValue,
    padicValRat.div hhalfMomentNe (mul_ne_zero hfactorialNe hpowNe),
    padicValRat.mul hfactorialNe hpowNe, padicValRat.pow,
    hvalTwo, hhalfMomentVal]
  ring

/-- Closed binary-weight form of the valuation at `2⁻ⁿ`, with the factorial
valuation eliminated by Legendre's formula. -/
theorem fabiusAtInverseTwoPow_padicVal_two_closed (n : ℕ) (hn : 1 ≤ n) :
    padicValRat 2 (fabiusAtInverseTwoPow n) =
      -(n.choose 2 : ℤ) - 1 - ((n - binaryWeight n : ℕ) : ℤ) := by
  rw [fabiusAtInverseTwoPow_padicVal_two n hn, factorial_padicVal_two]

end Fabius
