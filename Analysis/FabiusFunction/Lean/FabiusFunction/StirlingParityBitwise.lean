import FabiusFunction.StirlingParity
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Bitwise

/-!
# The bitwise parity criterion, and Kummer's theorem at the prime two

`StirlingParity` reduces the parity of a second-kind Stirling number to a binomial
coefficient: `S(n,k) ≡ C(n - (k+2)/2, (k-1)/2) (mod 2)`.  This module supplies the other
half of the source's parity theorem, namely when that binomial coefficient is odd.

The answer is Kummer's theorem at `p = 2`: `C(w+d, w)` is odd exactly when adding `w` and `d`
in base two produces no carry, that is, when `w &&& d = 0` (`odd_choose_add_iff`).  Mathlib
has Lucas's theorem but not this carry consequence — and the corpus module
`ThueMorseLucasSupport` carries only the submask form, `Odd (n.choose k) ↔ k &&& n = k`, which
does not yield the carry form without a further induction — so it is proved here by induction
on `w`,
peeling one binary digit per step; the four parity cases split into three where the digits do
not collide — and the induction hypothesis applies verbatim — and one where they do, in which
both sides fail at once.

Combining the two gives the criterion the source states, `S(n,k)` odd iff
`(k-1)/2 &&& (n-k) = 0` (`stirlingSecond_odd_iff`), and then the central case
`S(2n,n)` (`stirlingSecond_two_mul_odd_iff`).  The central case is odd exactly for those `n`
whose binary expansion has no two adjacent `1`-bits — *not*, as one might guess from small
values, exactly for the powers of two: `n = 5` is the smallest counterexample, with
`S(10,5) = 42525` odd.

## Main results

* `odd_choose_add_iff`, Kummer's theorem at the prime two.
* `stirlingSecond_odd_iff`, the bitwise parity criterion.
* `stirlingSecond_two_mul_odd_iff`, the central case.
-/

set_option autoImplicit false

namespace Fabius

/-- A natural number vanishes exactly when every one of its binary digits does. -/
theorem eq_zero_iff_testBit (x : ℕ) : x = 0 ↔ ∀ i, x.testBit i = false := by
  constructor
  · rintro rfl i
    exact Nat.zero_testBit i
  · intro h
    exact Nat.eq_of_testBit_eq fun i => by rw [h i, Nat.zero_testBit]

/-- `a &&& b` vanishes exactly when `a` and `b` share no `1`-bit. -/
theorem land_eq_zero_iff (a b : ℕ) :
    a &&& b = 0 ↔ ∀ i, a.testBit i = false ∨ b.testBit i = false := by
  rw [eq_zero_iff_testBit]
  refine forall_congr' fun i => ?_
  rw [Nat.testBit_land]
  cases a.testBit i <;> cases b.testBit i <;> simp

/-- Disjointness of binary digits, with the lowest digit peeled off.  This is the step the
induction of `odd_choose_add_iff` runs on. -/
theorem land_eq_zero_iff_div_two (a b : ℕ) :
    a &&& b = 0 ↔
      (a.testBit 0 = false ∨ b.testBit 0 = false) ∧ (a / 2) &&& (b / 2) = 0 := by
  rw [land_eq_zero_iff, land_eq_zero_iff]
  constructor
  · intro h
    refine ⟨h 0, fun i => ?_⟩
    rw [← Nat.testBit_add_one, ← Nat.testBit_add_one]
    exact h (i + 1)
  · rintro ⟨h0, hrec⟩ i
    cases i with
    | zero => exact h0
    | succ j =>
      have h := hrec j
      rwa [← Nat.testBit_add_one, ← Nat.testBit_add_one] at h

/-- The step of Kummer's theorem at `p = 2` in the case where the lowest digits of `w` and `d`
do not collide.  Lucas's theorem splits the binomial coefficient into a digit factor, which
the hypothesis `hsmall` makes equal to `1`, and a factor at the halved arguments, to which the
induction hypothesis applies. -/
theorem odd_choose_add_of_no_carry {w d : ℕ}
    (hsmall : ((w + d) % 2).choose (w % 2) = 1)
    (hdiv : (w + d) / 2 = w / 2 + d / 2)
    (hbit : w.testBit 0 = false ∨ d.testBit 0 = false)
    (ih : Odd ((w / 2 + d / 2).choose (w / 2)) ↔ (w / 2) &&& (d / 2) = 0) :
    Odd ((w + d).choose w) ↔ w &&& d = 0 := by
  have hlucas : Nat.ModEq 2 ((w + d).choose w)
      (((w + d) % 2).choose (w % 2) * ((w + d) / 2).choose (w / 2)) :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have hlucas' : (w + d).choose w % 2
      = (((w + d) % 2).choose (w % 2) * ((w + d) / 2).choose (w / 2)) % 2 := hlucas
  have hsplit : Odd ((w + d).choose w) ↔ Odd (((w + d) / 2).choose (w / 2)) := by
    rw [Nat.odd_iff, hlucas', hsmall, one_mul, ← Nat.odd_iff]
  rw [hsplit, hdiv, ih, land_eq_zero_iff_div_two w d]
  exact (and_iff_right hbit).symm

/-- **Kummer's theorem at the prime two.**  The binomial coefficient `C(w+d, w)` is odd
exactly when adding `w` and `d` in base two produces no carry, that is, when the two have no
`1`-bit in common. -/
theorem odd_choose_add_iff (w d : ℕ) : Odd ((w + d).choose w) ↔ w &&& d = 0 := by
  induction w using Nat.strong_induction_on generalizing d with
  | _ w ih =>
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · simp
    · have hlt : w / 2 < w := Nat.div_lt_self hw (by norm_num)
      rcases Nat.mod_two_eq_zero_or_one w with hw2 | hw2 <;>
        rcases Nat.mod_two_eq_zero_or_one d with hd2 | hd2
      · exact odd_choose_add_of_no_carry
          (by rw [show (w + d) % 2 = 0 by omega, hw2]; rfl) (by omega)
          (Or.inl (Nat.mod_two_eq_zero_iff_testBit_zero.mp hw2)) (ih _ hlt _)
      · exact odd_choose_add_of_no_carry
          (by rw [show (w + d) % 2 = 1 by omega, hw2]; rfl) (by omega)
          (Or.inl (Nat.mod_two_eq_zero_iff_testBit_zero.mp hw2)) (ih _ hlt _)
      · exact odd_choose_add_of_no_carry
          (by rw [show (w + d) % 2 = 1 by omega, hw2]; rfl) (by omega)
          (Or.inr (Nat.mod_two_eq_zero_iff_testBit_zero.mp hd2)) (ih _ hlt _)
      · -- both lowest digits are `1`: the addition carries, and both sides fail
        have h0 : ((w + d) % 2).choose (w % 2) = 0 := by
          rw [show (w + d) % 2 = 0 by omega, hw2]; rfl
        have hlucas : Nat.ModEq 2 ((w + d).choose w)
            (((w + d) % 2).choose (w % 2) * ((w + d) / 2).choose (w / 2)) :=
          Choose.choose_modEq_choose_mod_mul_choose_div_nat
        have hlucas' : (w + d).choose w % 2
            = (((w + d) % 2).choose (w % 2) * ((w + d) / 2).choose (w / 2)) % 2 := hlucas
        constructor
        · intro hodd
          rw [Nat.odd_iff, hlucas', h0, zero_mul] at hodd
          simp at hodd
        · intro hzero
          rw [land_eq_zero_iff] at hzero
          have h := hzero 0
          rw [Nat.mod_two_eq_one_iff_testBit_zero.mp hw2,
            Nat.mod_two_eq_one_iff_testBit_zero.mp hd2] at h
          simp at h

/-- Kummer's theorem at the prime two, in subtractive form: for `w ≤ z`, the binomial
coefficient `C(z,w)` is odd exactly when `w` and `z - w` share no `1`-bit.

This is the shape the Stirling criterion needs.  It is not the same statement as
`odd_choose_iff_land` of `ThueMorseLucasSupport`, which gives Lucas's criterion in the submask
form `Odd (n.choose k) ↔ k &&& n = k`; passing between the two costs an induction of its own,
so the corpus carries both. -/
theorem odd_choose_iff_land_sub {z w : ℕ} (hw : w ≤ z) :
    Odd (z.choose w) ↔ w &&& (z - w) = 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, z = w + d := ⟨z - w, by omega⟩
  rw [Nat.add_sub_cancel_left]
  exact odd_choose_add_iff w d

/-- **The bitwise parity criterion for the Stirling numbers of the second kind.**  For
`1 ≤ k ≤ n`, the number `S(n,k)` is odd exactly when `n - k` and `⌊(k-1)/2⌋` share no
`1`-bit. -/
theorem stirlingSecond_odd_iff {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    Odd (Nat.stirlingSecond n k) ↔ ((k - 1) / 2) &&& (n - k) = 0 := by
  have hmod : Nat.stirlingSecond n k % 2 = (n - (k + 2) / 2).choose ((k - 1) / 2) % 2 :=
    stirlingSecond_modEq_choose_two hk hkn
  have h1 : Odd (Nat.stirlingSecond n k) ↔ Odd ((n - (k + 2) / 2).choose ((k - 1) / 2)) := by
    rw [Nat.odd_iff, Nat.odd_iff, hmod]
  rw [h1, odd_choose_iff_land_sub (by omega : (k - 1) / 2 ≤ n - (k + 2) / 2),
    show n - (k + 2) / 2 - (k - 1) / 2 = n - k by omega]

/-- Subtracting one before halving does not change whether a number meets its own halved
self bitwise.  The even case is where the content lies: for `n = 2m` both sides halve to a
statement about `m` and `⌊(m-1)/2⌋` respectively, which is the induction hypothesis at `m`. -/
theorem land_pred_div_two_iff :
    ∀ n : ℕ, 1 ≤ n → (n &&& ((n - 1) / 2) = 0 ↔ n &&& (n / 2) = 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨m, rfl⟩ := he
      have hm : 1 ≤ m := by omega
      have hb0 : (m + m).testBit 0 = false :=
        Nat.mod_two_eq_zero_iff_testBit_zero.mp (by omega)
      rw [land_eq_zero_iff_div_two (m + m) ((m + m - 1) / 2),
        land_eq_zero_iff_div_two (m + m) ((m + m) / 2),
        show (m + m - 1) / 2 = m - 1 by omega, show (m + m) / 2 = m by omega,
        and_iff_right (Or.inl hb0), and_iff_right (Or.inl hb0)]
      exact ih m (by omega) hm
    · obtain ⟨m, rfl⟩ := ho
      rw [show (2 * m + 1 - 1) / 2 = (2 * m + 1) / 2 by omega]

/-- A number meets its own doubling bitwise exactly when it meets its own halving: both say
that no two adjacent binary digits of `n` are `1`. -/
theorem land_two_mul_iff (n : ℕ) : n &&& (2 * n) = 0 ↔ n &&& (n / 2) = 0 := by
  rw [land_eq_zero_iff, land_eq_zero_iff]
  have hhalf : ∀ i, (n / 2).testBit i = n.testBit (i + 1) := fun i =>
    (Nat.testBit_add_one n i).symm
  have hdouble : ∀ i, (2 * n).testBit (i + 1) = n.testBit i := fun i => by
    rw [Nat.testBit_add_one, show 2 * n / 2 = n by omega]
  constructor
  · intro h i
    rw [hhalf]
    exact (h (i + 1)).symm.imp (fun hb => by rwa [hdouble] at hb) id
  · intro h i
    cases i with
    | zero => exact Or.inr (Nat.mod_two_eq_zero_iff_testBit_zero.mp (by omega))
    | succ j =>
      rw [hdouble]
      exact ((h j).imp id fun hb => by rwa [hhalf] at hb).symm

/-- **The central second-kind number.**  For `n ≥ 1`, the Stirling number `S(2n, n)` is odd
exactly when the binary expansion of `n` has no two adjacent `1`-bits.  The powers of two are
the `n` with a *single* `1`-bit, a strictly smaller class: `n = 5` also qualifies, and indeed
`S(10,5) = 42525` is odd. -/
theorem stirlingSecond_two_mul_odd_iff {n : ℕ} (hn : 1 ≤ n) :
    Odd (Nat.stirlingSecond (2 * n) n) ↔ n &&& (2 * n) = 0 := by
  rw [stirlingSecond_odd_iff hn (by omega), show 2 * n - n = n by omega,
    Nat.land_comm ((n - 1) / 2) n, land_pred_div_two_iff n hn, land_two_mul_iff]

end Fabius
