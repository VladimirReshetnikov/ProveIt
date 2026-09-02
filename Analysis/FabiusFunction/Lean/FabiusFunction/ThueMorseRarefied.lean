import FabiusFunction.ThueMorseEnumerators
import FabiusFunction.ThueMorseNewman

/-!
# Rarefied Thue--Morse sums and Newman's phenomenon at dyadic endpoints

Restricting the signed Thue--Morse sequence to an arithmetic progression
destroys its bounded-discrepancy balance.  This module proves the exact
statements of the atlas's rarefaction chapter at dyadic endpoints:

* `rarefiedSum` — the signed sum over a residue class
  `{n < 2^m : n ≡ r (mod q)}`, i.e. `thueMorseResidueSum` of
  `ThueMorseNewman` at the dyadic cutoff `2^m` — and the one-step
  recursion that halving induces for every odd modulus and **every even
  cutoff** (`thueMorseResidueSum_two_mul_of_odd`),
  `T_r(2M) = T_{2⁻¹r}(M) - T_{2⁻¹(r-1)}(M)`, whose dyadic instance
  is `A(m+1, r) = A(m, 2⁻¹r) - A(m, 2⁻¹(r-1))` and whose `q = 3`
  case reads `A(m+1, r) = A(m, 2r mod 3) - A(m, (2r+1) mod 3)`;
* the **closed vectors modulo three**:
  `(A₀, A₁, A₂)(2u+1) = 3^u · (1, -1, 0)` and
  `(A₀, A₁, A₂)(2u+2) = 3^u · (2, -1, -1)`;
* **Newman's phenomenon at dyadic endpoints**: `A₀(m) > 0` for every
  `m ≥ 1` — among multiples of three in a dyadic block, evil numbers
  always outnumber odious ones — with the exact growth `3^(m/2)` visible
  in the closed forms;
* the **balance of the full block** and the **even-modulus collapse**:
  restricting to the even numbers gives exact cancellation for `m ≥ 2`,
  so the excess is genuinely a property of odd moduli.

Everything is elementary induction on the block level; no root of unity
and no analysis appears.  The root-of-unity filter of the atlas is
subsumed by the closed forms.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## Rarefied sums and the one-step recursion for odd moduli -/

/-- The signed Thue--Morse sum over the residue class `r` modulo `q`,
within the dyadic block `range (2^m)`: the residue sum
`thueMorseResidueSum` of `ThueMorseNewman` at the dyadic cutoff
`2^m`. -/
def rarefiedSum (q r m : ℕ) : ℤ :=
  thueMorseResidueSum q r (2 ^ m)

/-- `rarefiedSum` unfolded to its defining block sum. -/
theorem rarefiedSum_eq (q r m : ℕ) :
    rarefiedSum q r m =
      ∑ n ∈ range (2 ^ m),
        if n % q = r then thueMorseSign n else 0 := rfl

/-- Doubling is invertible modulo an odd modulus:
`2j ≡ 2a (mod q) ↔ j ≡ a (mod q)` for odd `q`.  Cancelling the factor two
is Mathlib's `Nat.ModEq.cancel_left_of_coprime`, available because an odd
modulus is coprime to two. -/
theorem two_mul_mod_iff (q : ℕ) (hq : q % 2 = 1) (j a : ℕ) :
    (2 * j) % q = (2 * a) % q ↔ j % q = a % q := by
  have hgcd : Nat.gcd q 2 = 1 := by
    rw [Nat.gcd_comm, Nat.gcd_rec, hq, Nat.gcd_one_left]
  constructor
  · intro h
    have h' : 2 * j ≡ 2 * a [MOD q] := h
    exact Nat.ModEq.cancel_left_of_coprime hgcd h'
  · intro h
    exact Nat.ModEq.mul_left 2 h

/-- **One-step recursion for every odd modulus and every even cutoff**
(the atlas's matrix recursion): splitting `range (2M)` by the lowest
binary digit sends the residue class `r` to the classes `2⁻¹r` (even
indices, same sign) and `2⁻¹(r-1)` (odd indices, opposite sign), the
halving realized by `2⁻¹ = (q+1)/2 (mod q)`.  Nothing dyadic is used:
the cutoff only has to be even.  The dyadic instance is
`rarefiedSum_succ_of_odd`. -/
theorem thueMorseResidueSum_two_mul_of_odd (q : ℕ) (hq : q % 2 = 1)
    (r M : ℕ) (hr : r < q) :
    thueMorseResidueSum q r (2 * M) =
      thueMorseResidueSum q (((q + 1) / 2 * r) % q) M -
        thueMorseResidueSum q (((q + 1) / 2 * (r + q - 1)) % q) M := by
  have hinv : ∀ x : ℕ, (2 * ((q + 1) / 2 * x)) % q = x % q := by
    intro x
    have hexp : 2 * ((q + 1) / 2 * x) = x + x * q := by
      have h2 : (q + 1) / 2 * 2 = q + 1 := by omega
      calc 2 * ((q + 1) / 2 * x) = ((q + 1) / 2 * 2) * x := by ring
        _ = (q + 1) * x := by rw [h2]
        _ = x + x * q := by ring
    rw [hexp, Nat.add_mul_mod_self_right]
  have hsplit : thueMorseResidueSum q r (2 * M) =
      ∑ j ∈ range M,
        ((if (2 * j) % q = r then thueMorseSign (2 * j) else 0) +
          (if (2 * j + 1) % q = r then thueMorseSign (2 * j + 1) else 0)) := by
    rw [thueMorseResidueSum,
      sum_range_two_mul M
        (fun n => if n % q = r then thueMorseSign n else 0)]
  rw [hsplit, thueMorseResidueSum, thueMorseResidueSum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hje : (2 * j) % q = r ↔ j % q = ((q + 1) / 2 * r) % q := by
    constructor
    · intro h
      refine (two_mul_mod_iff q hq j ((q + 1) / 2 * r)).mp ?_
      rw [hinv r, Nat.mod_eq_of_lt hr]
      exact h
    · intro h
      have h2 := (two_mul_mod_iff q hq j ((q + 1) / 2 * r)).mpr h
      rwa [hinv r, Nat.mod_eq_of_lt hr] at h2
  have hjo : (2 * j + 1) % q = r ↔
      j % q = ((q + 1) / 2 * (r + q - 1)) % q := by
    have hshift : (2 * j + 1) % q = r ↔ (2 * j) % q = (r + q - 1) % q := by
      constructor
      · intro h
        have hm : (2 * j + 1) % q = r % q := by
          rw [Nat.mod_eq_of_lt hr]; exact h
        have h1 : (2 * j + 1 + (q - 1)) % q = (r + (q - 1)) % q :=
          Nat.ModEq.add_right (q - 1) hm
        rwa [show 2 * j + 1 + (q - 1) = 2 * j + q by omega,
          Nat.add_mod_right, show r + (q - 1) = r + q - 1 by omega] at h1
      · intro h
        have h1 : (2 * j + 1) % q = (r + q - 1 + 1) % q :=
          Nat.ModEq.add_right 1 h
        rwa [show r + q - 1 + 1 = r + q by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt hr] at h1
    rw [hshift]
    constructor
    · intro h
      refine (two_mul_mod_iff q hq j ((q + 1) / 2 * (r + q - 1))).mp ?_
      rw [hinv (r + q - 1)]
      exact h
    · intro h
      have h2 := (two_mul_mod_iff q hq j ((q + 1) / 2 * (r + q - 1))).mpr h
      rwa [hinv (r + q - 1)] at h2
  rw [thueMorseSign_two_mul, thueMorseSign_two_mul_add_one]
  by_cases he : j % q = ((q + 1) / 2 * r) % q <;>
    by_cases ho : j % q = ((q + 1) / 2 * (r + q - 1)) % q
  · rw [if_pos (hje.mpr he), if_pos (hjo.mpr ho), if_pos he, if_pos ho]
    ring
  · rw [if_pos (hje.mpr he), if_neg (fun h => ho (hjo.mp h)),
      if_pos he, if_neg ho]
    ring
  · rw [if_neg (fun h => he (hje.mp h)), if_pos (hjo.mpr ho),
      if_neg he, if_pos ho]
    ring
  · rw [if_neg (fun h => he (hje.mp h)), if_neg (fun h => ho (hjo.mp h)),
      if_neg he, if_neg ho]
    ring

/-- **One-step recursion for every odd modulus at dyadic cutoffs**: the
instance `M = 2^m` of `thueMorseResidueSum_two_mul_of_odd`, in the
`rarefiedSum` notation.  Modulo three this specializes to
`rarefiedSum_three_succ`. -/
theorem rarefiedSum_succ_of_odd (q : ℕ) (hq : q % 2 = 1)
    (r m : ℕ) (hr : r < q) :
    rarefiedSum q r (m + 1) =
      rarefiedSum q (((q + 1) / 2 * r) % q) m -
        rarefiedSum q (((q + 1) / 2 * (r + q - 1)) % q) m := by
  unfold rarefiedSum
  rw [pow_succ, mul_comm (2 ^ m) 2]
  exact thueMorseResidueSum_two_mul_of_odd q hq r (2 ^ m) hr

/-- **One-step recursion modulo three** — the `q = 3` case of
`rarefiedSum_succ_of_odd`, in which `2⁻¹ = 2 (mod 3)` and both residues
are written out.  Splitting a block by the lowest binary digit sends the
class `r` to the classes `2r` (even indices, same sign) and `2r + 1`
(odd indices, opposite sign), reduced modulo three. -/
theorem rarefiedSum_three_succ (r m : ℕ) (hr : r < 3) :
    rarefiedSum 3 r (m + 1) =
      rarefiedSum 3 (2 * r % 3) m - rarefiedSum 3 ((2 * r + 1) % 3) m := by
  have h := rarefiedSum_succ_of_odd 3 (by omega) r m hr
  rw [show (3 + 1) / 2 = 2 from by omega,
    show 2 * (r + 3 - 1) % 3 = (2 * r + 1) % 3 from by omega] at h
  exact h

/-! ## Closed vectors modulo three -/

/-- **Exact dyadic rarefaction modulo three.**  The residue vector of a
dyadic block is `3^u·(1,-1,0)` at the odd level `2u+1` and
`3^u·(2,-1,-1)` at the even level `2u+2`: the excess on multiples of
three grows by a factor of three every two levels. -/
theorem rarefiedSum_three_closed (u : ℕ) :
    (rarefiedSum 3 0 (2 * u + 1) = 3 ^ u ∧
      rarefiedSum 3 1 (2 * u + 1) = -(3 ^ u) ∧
        rarefiedSum 3 2 (2 * u + 1) = 0) ∧
    (rarefiedSum 3 0 (2 * u + 2) = 2 * 3 ^ u ∧
      rarefiedSum 3 1 (2 * u + 2) = -(3 ^ u) ∧
        rarefiedSum 3 2 (2 * u + 2) = -(3 ^ u)) := by
  induction u with
  | zero =>
      have h00 : rarefiedSum 3 0 0 = 1 := by
        simp [rarefiedSum, thueMorseResidueSum, thueMorseSign,
          binaryWeight]
      have h01 : rarefiedSum 3 1 0 = 0 := by
        simp [rarefiedSum, thueMorseResidueSum, thueMorseSign,
          binaryWeight]
      have h02 : rarefiedSum 3 2 0 = 0 := by
        simp [rarefiedSum, thueMorseResidueSum, thueMorseSign,
          binaryWeight]
      have e0 := rarefiedSum_three_succ 0 0 (by omega)
      have e1 := rarefiedSum_three_succ 1 0 (by omega)
      have e2 := rarefiedSum_three_succ 2 0 (by omega)
      have j0 := rarefiedSum_three_succ 0 1 (by omega)
      have j1 := rarefiedSum_three_succ 1 1 (by omega)
      have j2 := rarefiedSum_three_succ 2 1 (by omega)
      norm_num at e0 e1 e2 j0 j1 j2
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
        · try norm_num
          linarith [e0, e1, e2, j0, j1, j2, h00, h01, h02]
  | succ u ih =>
      obtain ⟨-, h0, h1, h2⟩ := ih
      have hp : (3 : ℤ) ^ (u + 1) = 3 * 3 ^ u := by
        rw [pow_succ]; ring
      have e0 := rarefiedSum_three_succ 0 (2 * u + 2) (by omega)
      have e1 := rarefiedSum_three_succ 1 (2 * u + 2) (by omega)
      have e2 := rarefiedSum_three_succ 2 (2 * u + 2) (by omega)
      have j0 := rarefiedSum_three_succ 0 (2 * u + 2 + 1) (by omega)
      have j1 := rarefiedSum_three_succ 1 (2 * u + 2 + 1) (by omega)
      have j2 := rarefiedSum_three_succ 2 (2 * u + 2 + 1) (by omega)
      norm_num at e0 e1 e2 j0 j1 j2
      constructor
      · refine ⟨?_, ?_, ?_⟩ <;>
          · rw [show 2 * (u + 1) + 1 = 2 * u + 2 + 1 by ring]
            linarith [e0, e1, e2, h0, h1, h2, hp]
      · refine ⟨?_, ?_, ?_⟩ <;>
          · rw [show 2 * (u + 1) + 2 = 2 * u + 2 + 1 + 1 by ring]
            linarith [e0, e1, e2, j0, j1, j2, h0, h1, h2, hp]

/-- Multiples of three at odd dyadic levels: exact excess `3^u`. -/
theorem rarefiedSum_three_zero_odd (u : ℕ) :
    rarefiedSum 3 0 (2 * u + 1) = 3 ^ u :=
  (rarefiedSum_three_closed u).1.1

/-- Multiples of three at even dyadic levels: exact excess `2·3^u`. -/
theorem rarefiedSum_three_zero_even (u : ℕ) :
    rarefiedSum 3 0 (2 * u + 2) = 2 * 3 ^ u :=
  (rarefiedSum_three_closed u).2.1

/-- **Newman's phenomenon at dyadic endpoints.**  In every dyadic block
`range (2^m)` with `m ≥ 1`, the multiples of three carry a strictly
positive signed sum: evil multiples of three outnumber odious ones. -/
theorem rarefiedSum_three_zero_pos (m : ℕ) (hm : 1 ≤ m) :
    0 < rarefiedSum 3 0 m := by
  rcases Nat.even_or_odd m with ⟨u, hu⟩ | ⟨u, hu⟩
  · have hu' : m = 2 * (u - 1) + 2 := by omega
    rw [hu', rarefiedSum_three_zero_even]
    positivity
  · rw [hu, rarefiedSum_three_zero_odd]
    positivity

/-! ## Balance of the full block and the even class -/

/-- The full dyadic block balances exactly for `m ≥ 1`: the instance
`M = 2^(m-1)` of `sum_thueMorseSign_two_mul` (every even prefix sum
vanishes). -/
theorem sum_thueMorseSign_range_two_pow (m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ range (2 ^ m), thueMorseSign n = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ, mul_comm (2 ^ k) 2]
  exact sum_thueMorseSign_two_mul (2 ^ k)

/-- **Even-modulus collapse.**  The even residue class balances exactly
for `m ≥ 2`: the rarefaction excess is a property of odd moduli only. -/
theorem rarefiedSum_two_zero (m : ℕ) (hm : 2 ≤ m) :
    rarefiedSum 2 0 m = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hsplit : rarefiedSum 2 0 (k + 1) =
      ∑ j ∈ range (2 ^ k),
        ((if (2 * j) % 2 = 0 then thueMorseSign (2 * j) else 0) +
          (if (2 * j + 1) % 2 = 0 then thueMorseSign (2 * j + 1) else 0)) := by
    rw [rarefiedSum, thueMorseResidueSum, pow_succ, mul_comm (2 ^ k) 2,
      sum_range_two_mul (2 ^ k)
        (fun n => if n % 2 = 0 then thueMorseSign n else 0)]
  rw [hsplit]
  have hterm : ∀ j ∈ range (2 ^ k),
      ((if (2 * j) % 2 = 0 then thueMorseSign (2 * j) else 0) +
        (if (2 * j + 1) % 2 = 0 then thueMorseSign (2 * j + 1) else 0)) =
        thueMorseSign j := by
    intro j _
    rw [if_pos (by omega), if_neg (by omega), thueMorseSign_two_mul]
    ring
  rw [Finset.sum_congr rfl hterm]
  exact sum_thueMorseSign_range_two_pow k (by omega)

/-! ## Root-of-unity vanishing -/

/-- **Root-of-unity vanishing.**  Over any commutative ring, the signed
block sum `∑_{n<2^m} ε(n)·z^n` vanishes whenever `z^(2^j) = 1` for some
`j < m` — the algebraic skeleton of the vanishing of the dyadic discrete
Fourier transform at all non-primitive frequencies. -/
theorem sum_thueMorseSign_mul_pow_eq_zero_of_pow_eq_one {R : Type*}
    [CommRing R] (z : R) (m j : ℕ) (hj : j < m) (hz : z ^ 2 ^ j = 1) :
    ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : R) * z ^ n = 0 := by
  rw [← prod_one_sub_pow_eq_sum_thueMorseSign]
  refine Finset.prod_eq_zero (Finset.mem_range.mpr hj) ?_
  rw [hz, sub_self]

end Fabius
