import FabiusFunction.ThueMorseEnumerators

/-!
# Rarefied Thue--Morse sums and Newman's phenomenon at dyadic endpoints

Restricting the signed Thue--Morse sequence to an arithmetic progression
destroys its bounded-discrepancy balance.  This module proves the exact
statements of the atlas's rarefaction chapter at dyadic endpoints:

* `rarefiedSum` — the signed sum over a residue class
  `{n < 2^m : n ≡ r (mod q)}` — and the one-step recursion that halving
  induces on residue classes modulo three:
  `A(m+1, r) = A(m, 2r mod 3) - A(m, (2r+1) mod 3)`;
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

/-! ## Rarefied sums and the modulo-three recursion -/

/-- The signed Thue--Morse sum over the residue class `r` modulo `q`,
within the dyadic block `range (2^m)`. -/
def rarefiedSum (q r m : ℕ) : ℤ :=
  ∑ n ∈ range (2 ^ m), if n % q = r then thueMorseSign n else 0

/-- **One-step recursion modulo three.**  Splitting a block by the lowest
binary digit sends the class `r` to the classes `2r` (even indices, same
sign) and `2r + 1` (odd indices, opposite sign), reduced modulo three. -/
theorem rarefiedSum_three_succ (r m : ℕ) (hr : r < 3) :
    rarefiedSum 3 r (m + 1) =
      rarefiedSum 3 (2 * r % 3) m - rarefiedSum 3 ((2 * r + 1) % 3) m := by
  have hsplit : rarefiedSum 3 r (m + 1) =
      ∑ j ∈ range (2 ^ m),
        ((if (2 * j) % 3 = r then thueMorseSign (2 * j) else 0) +
          (if (2 * j + 1) % 3 = r then thueMorseSign (2 * j + 1) else 0)) := by
    rw [rarefiedSum, pow_succ, mul_comm (2 ^ m) 2,
      sum_range_two_mul (2 ^ m)
        (fun n => if n % 3 = r then thueMorseSign n else 0)]
  rw [hsplit, rarefiedSum, rarefiedSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hje : (2 * j) % 3 = r ↔ j % 3 = 2 * r % 3 := by omega
  have hjo : (2 * j + 1) % 3 = r ↔ j % 3 = (2 * r + 1) % 3 := by omega
  rw [thueMorseSign_two_mul, thueMorseSign_two_mul_add_one]
  by_cases he : j % 3 = 2 * r % 3 <;> by_cases ho : j % 3 = (2 * r + 1) % 3
  · omega
  · rw [if_pos (hje.mpr he), if_neg (fun h => ho (hjo.mp h)),
      if_pos he, if_neg ho]
    ring
  · rw [if_neg (fun h => he (hje.mp h)), if_pos (hjo.mpr ho),
      if_neg he, if_pos ho]
    ring
  · rw [if_neg (fun h => he (hje.mp h)), if_neg (fun h => ho (hjo.mp h)),
      if_neg he, if_neg ho]
    ring

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
        simp [rarefiedSum, thueMorseSign, binaryWeight]
      have h01 : rarefiedSum 3 1 0 = 0 := by
        simp [rarefiedSum, thueMorseSign, binaryWeight]
      have h02 : rarefiedSum 3 2 0 = 0 := by
        simp [rarefiedSum, thueMorseSign, binaryWeight]
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

/-- The full dyadic block balances exactly for `m ≥ 1`. -/
theorem sum_thueMorseSign_range_two_pow (m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ range (2 ^ m), thueMorseSign n = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ, mul_comm (2 ^ k) 2, sum_range_two_mul (2 ^ k) thueMorseSign]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [thueMorseSign_two_mul, thueMorseSign_two_mul_add_one]
  ring

/-- **Even-modulus collapse.**  The even residue class balances exactly
for `m ≥ 2`: the rarefaction excess is a property of odd moduli only. -/
theorem rarefiedSum_two_zero (m : ℕ) (hm : 2 ≤ m) :
    rarefiedSum 2 0 m = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hsplit : rarefiedSum 2 0 (k + 1) =
      ∑ j ∈ range (2 ^ k),
        ((if (2 * j) % 2 = 0 then thueMorseSign (2 * j) else 0) +
          (if (2 * j + 1) % 2 = 0 then thueMorseSign (2 * j + 1) else 0)) := by
    rw [rarefiedSum, pow_succ, mul_comm (2 ^ k) 2,
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

end Fabius
