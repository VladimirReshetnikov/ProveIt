import FabiusFunction.SumsOfSquaresGeneratingFunction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Jacobi's two-square theorem: the divisor sum, the vanishing half, and the Lambert series

The printed statement (`qg:thm-two-square`) is: for every `n ≥ 1`,

  `r₂(n) = 4 ∑_{d ∣ n} χ₄(d)`,   (`eq:qg-two-square`)

equivalently, writing `n = 2^a ∏ pⱼ^{αⱼ} ∏ r_ℓ^{β_ℓ}` with `pⱼ ≡ 1` and `r_ℓ ≡ 3 (mod 4)`,
`r₂(n) = 0` if some `β_ℓ` is odd and `r₂(n) = 4 ∏ (αⱼ + 1)` otherwise.  Its corollary
(`qg:cor-two-square-lambert`) is, for `|q| < 1`,

  `(∑_{m ∈ ℤ} q^{m²})² = 1 + 4 ∑_{d ≥ 1} χ₄(d) q^d/(1 - q^d)
                       = 1 + 4 ∑_{j ≥ 0} (-1)^j q^{2j+1}/(1 - q^{2j+1})`.
                                                       (`eq:qg-two-square-lambert`)

Here `r_d(n) = sumSqRep d n` counts ordered `d`-tuples of integers with `x₁² + ⋯ + x_d² = n`.

## What this module proves (everything below is unconditional and `sorry`-free)

Write `D n = twoSquareDivisorSum n = ∑_{d ∣ n} χ₄(d)`, the right-hand side of
`eq:qg-two-square` divided by `4`.

* **The equivalence of the two right-hand sides in `qg:thm-two-square`, in full.**  `D` is the
  Dirichlet convolution `ζ * χ₄` (`twoSquareArith`), hence multiplicative
  (`isMultiplicative_twoSquareArith`, `twoSquareDivisorSum_mul_of_coprime`); its local factors
  are computed exactly (`twoSquareDivisorSum_prime_pow`): `1` at `p = 2`, `k + 1` at
  `p ≡ 1 (mod 4)`, and `1` or `0` according as `k` is even or odd at `p ≡ 3 (mod 4)`.  Hence
  `D n = 0` exactly when some prime `≡ 3 (mod 4)` occurs to an odd power
  (`twoSquareDivisorSum_eq_zero_iff`, `twoSquareDivisorSum_ne_zero_iff`), and otherwise
  `D n = ∏_{p ≡ 1 (4)} (v_p(n) + 1)` (`twoSquareDivisorSum_eq_prod`).  So `4 · D n` is `0`
  exactly when some `β_ℓ` is odd and is `4 ∏ (αⱼ + 1)` otherwise: this is precisely the step
  the printed proof dispatches with "The divisor sum is multiplicative."  The corresponding
  statement about `r₂(n)` needs, in addition, `eq:qg-two-square` itself — proved here only
  where both of its sides vanish, see below.

* **The vanishing half of `qg:thm-two-square`, in full.**  For `n ≠ 0`,
  `sumSqRep 2 n = 0 ↔ D n = 0` (`sumSqRep_two_eq_zero_iff`), from Mathlib's
  `Nat.eq_sq_add_sq_iff` and the local factors above; so `eq:qg-two-square` itself is proved
  here on the whole set where both of its sides vanish
  (`sumSqRep_two_eq_four_mul_of_eq_zero`).

* **A general Lambert-series theorem** (`hasSum_lambert`), the rearrangement the printed
  corollary uses without justification: for *any* coefficients `a : ℕ → 𝕜` with `‖a n‖ ≤ C`
  over *any* complete normed field and any `‖q‖ < 1`,
  `∑_{n ≥ 0} (∑_{d ∣ n} a d) q^n = ∑'_d a d q^d/(1 - q^d)`.  The proof is absolute
  convergence on `ℕ × ℕ` (`summable_lambertPairs`) followed by the regrouping
  `hasSum_regroup` along the fibres `lambertFiber n = {(i, j) | (i+1)(j+1) = n}`, which are
  matched with `Nat.divisorsAntidiagonal` (`sum_lambertFiber`).  Specialised to `χ₄` this is
  `hasSum_twoSquareDivisorSum_lambert`.

* **The second equality of `eq:qg-two-square-lambert`, unconditionally**
  (`tsum_chi4_lambert_eq_tsum_odd`):
  `∑'_d χ₄(d) q^d/(1 - q^d) = ∑'_j (-1)^j q^{2j+1}/(1 - q^{2j+1})`, because `χ₄` vanishes on
  even arguments and equals `(-1)^j` at `2j+1`.

* **The corollary, reduced to the arithmetic core.**  `hasSum_theta_sq_lambert` and
  `theta_sq_eq_lambert_odd` prove both displayed equalities of `eq:qg-two-square-lambert`
  from the single hypothesis `∀ n ≠ 0, (r₂(n) : ℤ) = 4 * D n`.  All the analysis is
  discharged, including the separate `n = 0` contribution `r₂(0) = 1` (`sumSqRep_two_zero`),
  which is where the leading `1` of the printed identity comes from.

## What is NOT covered

The identity `r₂(n) = 4 · D n` itself is proved here **only where both sides vanish**.  For
`n` that *is* a sum of two squares the counting statement is left open: it needs the number of
Gaussian integers of norm `n`, i.e. unique factorisation in `ℤ[i]`, the four units, and — the
step the printed proof compresses into the word "nonduplicative" — that `ϖ` and `ϖ̄` are
non-associate for `p ≡ 1 (mod 4)`, so that the `αⱼ + 1` choices of exponent really are
distinct.  (The printed argument is correct; it simply leaves that verification implicit,
and `qg:lem-gaussian-ufd` records uniqueness only "up to a unit and conjugation".)  Mathlib
has no count of Gaussian integers of given norm and no Jacobi two-square theorem
(`Mathlib.NumberTheory.SumTwoSquares` gives only the existence characterisation).
`hasSum_theta_sq_lambert` takes exactly that missing input as a hypothesis, so
`qg:cor-two-square-lambert` closes the moment it lands.

## Generality beyond the print

The print states the corollary for `q ∈ ℂ` with `|q| < 1`.  Everything analytic here is stated
for an arbitrary `[NormedField 𝕜] [CompleteSpace 𝕜]` (matching `hasSum_sumSqRep`), and
`hasSum_lambert` is proved for arbitrary norm-bounded coefficients rather than for `χ₄`, so it
also covers the `σ₁` and four-square Lambert series of the same chapter.  `sum_lambertFiber`
and `tsum_chi4_lambert_eq_tsum_odd` do not use completeness at all, and
`norm_intCast_chi4_le_one` holds over any normed field.  The Lambert index runs over `ℕ`
rather than `ℕ_{≥1}`: the `d = 0` term is `a 0 · q⁰/(1 - q⁰) = a 0 / 0 = 0` and
`Nat.divisors 0 = ∅`, so no `ℕ+` juggling is needed.

`sumSqFiber_two_zero` / `sumSqRep_two_zero` restate at `d = 2` facts that the sibling module
`FabiusFunction.FourSquareTheorem` also records for general `d` (as `sumSqFiber_zero` /
`sumSqRep_zero`); they are deliberately given different names, and proved again here, so that
this module depends only on `SumsOfSquaresGeneratingFunction`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## The character `χ₄` -/

/-- The nontrivial quadratic character mod `4`, as an integer-valued function on `ℕ`. -/
def chi4 (d : ℕ) : ℤ := ZMod.χ₄ (d : ZMod 4)

/-- `χ₄` is `0` on even arguments, `1` on `1 (mod 4)` and `-1` on `3 (mod 4)`. -/
theorem chi4_eq_ite (d : ℕ) :
    chi4 d = if d % 2 = 0 then 0 else if d % 4 = 1 then 1 else -1 :=
  ZMod.χ₄_nat_eq_if_mod_four d

/-- `χ₄` vanishes on even arguments. -/
theorem chi4_of_even {d : ℕ} (h : d % 2 = 0) : chi4 d = 0 := by
  rw [chi4_eq_ite, if_pos h]

/-- `χ₄(d) = 1` for `d ≡ 1 (mod 4)`. -/
theorem chi4_one_mod_four {d : ℕ} (h : d % 4 = 1) : chi4 d = 1 :=
  ZMod.χ₄_nat_one_mod_four h

/-- `χ₄(d) = -1` for `d ≡ 3 (mod 4)`. -/
theorem chi4_three_mod_four {d : ℕ} (h : d % 4 = 3) : chi4 d = -1 :=
  ZMod.χ₄_nat_three_mod_four h

/-- `χ₄(0) = 0`. -/
theorem chi4_zero : chi4 0 = 0 := chi4_of_even rfl

/-- `χ₄(1) = 1`. -/
theorem chi4_one : chi4 1 = 1 := chi4_one_mod_four rfl

/-- `χ₄(2) = 0`. -/
theorem chi4_two : chi4 2 = 0 := chi4_of_even rfl

/-- `χ₄(2j + 1) = (-1)^j`: the alternating form used in the second half of
`eq:qg-two-square-lambert`. -/
theorem chi4_two_mul_add_one (j : ℕ) : chi4 (2 * j + 1) = (-1 : ℤ) ^ j := by
  have h : (2 * j + 1) % 2 = 1 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  have h3 := ZMod.χ₄_eq_neg_one_pow h
  rw [h2] at h3
  exact h3

/-- `χ₄` is completely multiplicative. -/
theorem chi4_mul (m n : ℕ) : chi4 (m * n) = chi4 m * chi4 n := by
  show ZMod.χ₄ ((m * n : ℕ) : ZMod 4) = ZMod.χ₄ (m : ZMod 4) * ZMod.χ₄ (n : ZMod 4)
  rw [Nat.cast_mul, map_mul]

/-- `χ₄(m^k) = χ₄(m)^k`. -/
theorem chi4_pow (m k : ℕ) : chi4 (m ^ k) = chi4 m ^ k := by
  show ZMod.χ₄ ((m ^ k : ℕ) : ZMod 4) = ZMod.χ₄ (m : ZMod 4) ^ k
  rw [Nat.cast_pow, map_pow]

/-- `χ₄` takes only the values `0, 1, -1`. -/
theorem chi4_eq_zero_or_one_or_neg_one (d : ℕ) : chi4 d = 0 ∨ chi4 d = 1 ∨ chi4 d = -1 := by
  rw [chi4_eq_ite]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- The image of `χ₄(d)` in any normed field has norm at most `1`.  This is the only bound the
Lambert series below needs, and it holds over an arbitrary normed field — no completeness. -/
theorem norm_intCast_chi4_le_one {𝕜 : Type*} [NormedField 𝕜] (d : ℕ) :
    ‖((chi4 d : ℤ) : 𝕜)‖ ≤ 1 := by
  rcases chi4_eq_zero_or_one_or_neg_one d with h | h | h <;> rw [h] <;> simp

/-! ## The divisor sum `D n = ∑_{d ∣ n} χ₄(d)` -/

/-- `χ₄` as an arithmetic function, i.e. extended by `0` at `0`. -/
def chi4Arith : ArithmeticFunction ℤ := ⟨fun n => if n = 0 then 0 else chi4 n, by simp⟩

/-- The defining equation of `chi4Arith`. -/
theorem chi4Arith_apply (n : ℕ) : chi4Arith n = if n = 0 then 0 else chi4 n := rfl

/-- `chi4Arith` is multiplicative, because `χ₄` is completely multiplicative. -/
theorem isMultiplicative_chi4Arith : chi4Arith.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · rw [chi4Arith_apply, if_neg (Nat.one_ne_zero : (1 : ℕ) ≠ 0), chi4_one]
  · intro m n hm hn _
    simp only [chi4Arith_apply]
    rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn]
    exact chi4_mul m n

/-- `D = ζ * χ₄` as a Dirichlet convolution. -/
def twoSquareArith : ArithmeticFunction ℤ :=
  ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) * chi4Arith

/-- `D n = ∑_{d ∣ n} χ₄(d)`, the right-hand side of `eq:qg-two-square` divided by `4`. -/
def twoSquareDivisorSum (n : ℕ) : ℤ := ∑ d ∈ n.divisors, chi4 d

/-- `D 0 = 0`, since `0` has no divisors. -/
theorem twoSquareDivisorSum_zero : twoSquareDivisorSum 0 = 0 := by
  unfold twoSquareDivisorSum
  rw [Nat.divisors_zero, Finset.sum_empty]

/-- The divisor sum is the Dirichlet convolution `ζ * χ₄`. -/
theorem twoSquareDivisorSum_eq_twoSquareArith (n : ℕ) :
    twoSquareDivisorSum n = twoSquareArith n := by
  have h : twoSquareArith n = ∑ i ∈ n.divisors, chi4Arith i := by
    show (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) * chi4Arith) n
      = ∑ i ∈ n.divisors, chi4Arith i
    exact ArithmeticFunction.coe_zeta_mul_apply
  rw [h]
  unfold twoSquareDivisorSum
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [chi4Arith_apply, if_neg (Nat.pos_of_mem_divisors hd).ne']

/-- **The divisor sum is multiplicative** — the sentence "The divisor sum is multiplicative."
of the printed proof, here proved. -/
theorem isMultiplicative_twoSquareArith : twoSquareArith.IsMultiplicative := by
  have h1 : (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
      ArithmeticFunction ℤ)).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast
  exact h1.mul isMultiplicative_chi4Arith

/-- `D(mn) = D(m) D(n)` for coprime `m, n`. -/
theorem twoSquareDivisorSum_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    twoSquareDivisorSum (m * n) = twoSquareDivisorSum m * twoSquareDivisorSum n := by
  simp only [twoSquareDivisorSum_eq_twoSquareArith]
  exact isMultiplicative_twoSquareArith.map_mul_of_coprime h

/-! ## The local factors at a prime power -/

/-- **The local factors of the divisor sum** (the second paragraph of the printed proof):
`D(p^k)` is `k + 1` at `p ≡ 1 (mod 4)`, is `1 - 1 + ⋯ + (-1)^k` at `p ≡ 3 (mod 4)`, and is `1`
at `p = 2`. -/
theorem twoSquareDivisorSum_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    twoSquareDivisorSum (p ^ k) =
      if p % 4 = 1 then (k : ℤ) + 1
      else if p % 4 = 3 then (if Even k then 1 else 0) else 1 := by
  have hsum : twoSquareDivisorSum (p ^ k) = ∑ i ∈ Finset.range (k + 1), chi4 p ^ i := by
    unfold twoSquareDivisorSum
    rw [Nat.sum_divisors_prime_pow hp]
    exact Finset.sum_congr rfl fun i _ => chi4_pow p i
  rw [hsum]
  rcases hp.eq_two_or_odd with h2 | hodd
  · subst h2
    have hz : ∑ i ∈ Finset.range (k + 1), (0 : ℤ) ^ i = 1 := by
      rw [zero_geom_sum, if_neg (by omega : ¬ (k + 1 = 0))]
    rw [if_neg (by decide : ¬ (2 : ℕ) % 4 = 1), if_neg (by decide : ¬ (2 : ℕ) % 4 = 3),
      chi4_two, hz]
  · have h14 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases h14 with h1 | h3
    · have hone : ∑ i ∈ Finset.range (k + 1), (1 : ℤ) ^ i = (k : ℤ) + 1 := by
        rw [one_geom_sum, Nat.cast_add, Nat.cast_one]
      rw [if_pos h1, chi4_one_mod_four h1, hone]
    · rw [if_neg (by omega : ¬ p % 4 = 1), if_pos h3, chi4_three_mod_four h3, neg_one_geom_sum]
      by_cases hk : Even k
      · have hk1 : ¬ Even (k + 1) := by
          rw [Nat.even_add_one]
          exact fun hcon => hcon hk
        rw [if_neg hk1, if_pos hk]
      · have hk1 : Even (k + 1) := by
          rw [Nat.even_add_one]
          exact hk
        rw [if_pos hk1, if_neg hk]

/-- The local factor at `p^k` is nonzero exactly when `p ≡ 3 (mod 4)` forces `k` to be even. -/
theorem twoSquareDivisorSum_prime_pow_ne_zero_iff {p : ℕ} (hp : p.Prime) (k : ℕ) :
    twoSquareDivisorSum (p ^ k) ≠ 0 ↔ (p % 4 = 3 → Even k) := by
  rw [twoSquareDivisorSum_prime_pow hp]
  by_cases h1 : p % 4 = 1
  · rw [if_pos h1]
    exact ⟨fun _ h3 => absurd h3 (by omega), fun _ => by omega⟩
  by_cases h3 : p % 4 = 3
  · rw [if_neg h1, if_pos h3]
    by_cases hk : Even k
    · rw [if_pos hk]
      exact ⟨fun _ _ => hk, fun _ => one_ne_zero⟩
    · rw [if_neg hk]
      exact ⟨fun hcon => (hcon rfl).elim, fun hall => absurd (hall h3) hk⟩
  · rw [if_neg h1, if_neg h3]
    exact ⟨fun _ hcon => absurd hcon h3, fun _ => one_ne_zero⟩

/-- The local factor at `p^k` is nonnegative. -/
theorem twoSquareDivisorSum_prime_pow_nonneg {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ twoSquareDivisorSum (p ^ k) := by
  rw [twoSquareDivisorSum_prime_pow hp]
  split_ifs <;> omega

/-! ## Global evaluation of the divisor sum -/

/-- `D n = ∏_p D(p^{v_p(n)})` for `n ≠ 0`. -/
theorem twoSquareDivisorSum_eq_prod_primeFactors {n : ℕ} (hn : n ≠ 0) :
    twoSquareDivisorSum n =
      ∏ p ∈ n.primeFactors, twoSquareDivisorSum (p ^ n.factorization p) := by
  rw [twoSquareDivisorSum_eq_twoSquareArith,
    ArithmeticFunction.IsMultiplicative.multiplicative_factorization
      twoSquareArith isMultiplicative_twoSquareArith hn,
    Nat.prod_factorization_eq_prod_primeFactors]
  exact Finset.prod_congr rfl fun p _ => (twoSquareDivisorSum_eq_twoSquareArith _).symm

/-- `D n ≥ 0` for every `n`. -/
theorem twoSquareDivisorSum_nonneg (n : ℕ) : 0 ≤ twoSquareDivisorSum n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact le_of_eq twoSquareDivisorSum_zero.symm
  · rw [twoSquareDivisorSum_eq_prod_primeFactors hn]
    exact Finset.prod_nonneg fun p hp =>
      twoSquareDivisorSum_prime_pow_nonneg (Nat.prime_of_mem_primeFactors hp) _

/-- **`D n ≠ 0` iff every prime `≡ 3 (mod 4)` occurs to an even power** — the criterion in the
"Equivalently" clause of `qg:thm-two-square`. -/
theorem twoSquareDivisorSum_ne_zero_iff {n : ℕ} (hn : n ≠ 0) :
    twoSquareDivisorSum n ≠ 0 ↔ ∀ p ∈ n.primeFactors, p % 4 = 3 → Even (n.factorization p) := by
  rw [twoSquareDivisorSum_eq_prod_primeFactors hn, Finset.prod_ne_zero_iff]
  exact forall_congr' fun p => imp_congr_right fun hp =>
    twoSquareDivisorSum_prime_pow_ne_zero_iff (Nat.prime_of_mem_primeFactors hp) _

/-- **`D n = 0` iff some prime `≡ 3 (mod 4)` occurs to an odd power.** -/
theorem twoSquareDivisorSum_eq_zero_iff {n : ℕ} (hn : n ≠ 0) :
    twoSquareDivisorSum n = 0 ↔ ∃ p ∈ n.primeFactors, p % 4 = 3 ∧ Odd (n.factorization p) := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    refine (twoSquareDivisorSum_ne_zero_iff hn).mpr (fun p hp h3 => ?_) h
    exact Nat.not_odd_iff_even.mp (hcon p hp h3)
  · rintro ⟨p, hp, h3, hodd⟩
    by_contra h
    exact Nat.not_even_iff_odd.mpr hodd ((twoSquareDivisorSum_ne_zero_iff hn).mp h p hp h3)

/-- **The product formula of `qg:thm-two-square`**: if no prime `≡ 3 (mod 4)` occurs to an odd
power then `D n = ∏_{p ≡ 1 (4)} (v_p(n) + 1)`, so that `4 D n` is exactly the printed
`4 ∏ (αⱼ + 1)`. -/
theorem twoSquareDivisorSum_eq_prod {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p ∈ n.primeFactors, p % 4 = 3 → Even (n.factorization p)) :
    twoSquareDivisorSum n =
      ∏ p ∈ Finset.filter (fun p : ℕ => p % 4 = 1) n.primeFactors,
        ((n.factorization p : ℤ) + 1) := by
  rw [twoSquareDivisorSum_eq_prod_primeFactors hn, Finset.prod_filter]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [twoSquareDivisorSum_prime_pow (Nat.prime_of_mem_primeFactors hp)]
  by_cases h1 : p % 4 = 1
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h3 : p % 4 = 3
    · rw [if_pos h3, if_pos (h p hp h3)]
    · rw [if_neg h3]

/-! ## The vanishing half of Jacobi's two-square theorem -/

/-- The only representation of `0` as a sum of two squares is the zero pair.  (The sibling
module `FourSquareTheorem` proves the same for general `d` under the name `sumSqFiber_zero`;
this specialised copy keeps the present module independent of it.) -/
theorem sumSqFiber_two_zero : sumSqFiber 2 0 = {0} := by
  ext x
  rw [mem_sumSqFiber, Finset.mem_singleton]
  constructor
  · intro h
    funext k
    have hk : (x k).natAbs ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Nat.zero_le _).mp h k (Finset.mem_univ k)
    have hk2 : (x k).natAbs = 0 := by
      by_contra hne
      have hpos : 0 < (x k).natAbs := Nat.pos_of_ne_zero hne
      have h1 : 1 ≤ (x k).natAbs ^ 2 := Nat.one_le_pow 2 _ hpos
      rw [hk] at h1
      omega
    exact Int.natAbs_eq_zero.mp hk2
  · intro h
    subst h
    simp

/-- `r₂(0) = 1`.  This is the term the printed proof of `qg:cor-two-square-lambert` never
mentions, and the reason the corollary carries a leading `1`. -/
theorem sumSqRep_two_zero : sumSqRep 2 0 = 1 := by
  show (sumSqFiber 2 0).card = 1
  simp [sumSqFiber_two_zero]

/-- `r₂(n) ≠ 0` exactly when `n` is a sum of two squares. -/
theorem sumSqRep_two_ne_zero_iff (n : ℕ) :
    sumSqRep 2 n ≠ 0 ↔ ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
  show (sumSqFiber 2 n).card ≠ 0 ↔ ∃ x y : ℕ, n = x ^ 2 + y ^ 2
  rw [Finset.card_ne_zero]
  constructor
  · rintro ⟨v, hv⟩
    rw [mem_sumSqFiber, Fin.sum_univ_two] at hv
    exact ⟨(v 0).natAbs, (v 1).natAbs, hv.symm⟩
  · rintro ⟨x, y, rfl⟩
    refine ⟨fun i : Fin 2 => if i = 0 then (x : ℤ) else (y : ℤ), ?_⟩
    rw [mem_sumSqFiber, Fin.sum_univ_two]
    have h0 : (if (0 : Fin 2) = 0 then (x : ℤ) else (y : ℤ)) = (x : ℤ) := if_pos rfl
    have h1 : (if (1 : Fin 2) = 0 then (x : ℤ) else (y : ℤ)) = (y : ℤ) := if_neg (by decide)
    show ((if (0 : Fin 2) = 0 then (x : ℤ) else (y : ℤ)).natAbs) ^ 2
        + ((if (1 : Fin 2) = 0 then (x : ℤ) else (y : ℤ)).natAbs) ^ 2 = x ^ 2 + y ^ 2
    rw [h0, h1]
    simp only [Int.natAbs_natCast]

/-- **The vanishing half of `qg:thm-two-square`**: for `n ≠ 0`, `r₂(n) = 0 ↔ D n = 0`. -/
theorem sumSqRep_two_eq_zero_iff {n : ℕ} (hn : n ≠ 0) :
    sumSqRep 2 n = 0 ↔ twoSquareDivisorSum n = 0 := by
  have hL : sumSqRep 2 n ≠ 0 ↔ ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (n.factorization q) := by
    rw [sumSqRep_two_ne_zero_iff, Nat.eq_sq_add_sq_iff]
    refine forall_congr' fun q => imp_congr_right fun hq => imp_congr_right fun _ => ?_
    rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hq)]
  have hR := twoSquareDivisorSum_ne_zero_iff hn
  constructor
  · intro h
    by_contra hcon
    exact hL.mpr (hR.mp hcon) h
  · intro h
    by_contra hcon
    exact hR.mpr (hL.mp hcon) h

/-- `eq:qg-two-square` on the set where both of its sides vanish: if `D n = 0` (equivalently,
some prime `≡ 3 (mod 4)` divides `n` to an odd power) then `r₂(n) = 4 D n`, both sides being
`0`. -/
theorem sumSqRep_two_eq_four_mul_of_eq_zero {n : ℕ} (hn : n ≠ 0)
    (h : twoSquareDivisorSum n = 0) : (sumSqRep 2 n : ℤ) = 4 * twoSquareDivisorSum n := by
  have h0 : sumSqRep 2 n = 0 := (sumSqRep_two_eq_zero_iff hn).mpr h
  rw [h, h0, mul_zero, Nat.cast_zero]

/-! ## Lambert series -/

/-- The fibre of `(i, j) ↦ (i+1)(j+1)` over `n`, as a finite set. -/
def lambertFiber (n : ℕ) : Finset (ℕ × ℕ) :=
  Finset.filter (fun p : ℕ × ℕ => (p.1 + 1) * (p.2 + 1) = n) (Finset.range n ×ˢ Finset.range n)

/-- Membership in `lambertFiber` is exactly the defining equation: the range bounds are
automatic, since `i + 1` and `j + 1` divide `(i+1)(j+1)`. -/
theorem mem_lambertFiber {n : ℕ} {p : ℕ × ℕ} :
    p ∈ lambertFiber n ↔ (p.1 + 1) * (p.2 + 1) = n := by
  unfold lambertFiber
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨⟨?_, ?_⟩, h⟩⟩
  · have hpos : 0 < (p.1 + 1) * (p.2 + 1) :=
      mul_pos (by omega : 0 < p.1 + 1) (by omega : 0 < p.2 + 1)
    have hn : 0 < n := by rw [← h]; exact hpos
    have h1 : p.1 + 1 ≤ n := Nat.le_of_dvd hn ⟨p.2 + 1, h.symm⟩
    omega
  · have hpos : 0 < (p.1 + 1) * (p.2 + 1) :=
      mul_pos (by omega : 0 < p.1 + 1) (by omega : 0 < p.2 + 1)
    have hn : 0 < n := by rw [← h]; exact hpos
    have h2 : p.2 + 1 ≤ n := Nat.le_of_dvd hn ⟨p.1 + 1, by rw [← h]; ring⟩
    omega

section Lambert

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

omit [CompleteSpace 𝕜] in
/-- Summing `a` over the fibre `lambertFiber n` is summing `a` over the divisors of `n`: the
shift `(i, j) ↦ (i+1, j+1)` matches `lambertFiber n` with `Nat.divisorsAntidiagonal n`.  Only
the additive structure is used; completeness is not needed. -/
theorem sum_lambertFiber (a : ℕ → 𝕜) (n : ℕ) :
    ∑ p ∈ lambertFiber n, a (p.1 + 1) = ∑ d ∈ n.divisors, a d := by
  have key : ∑ p ∈ lambertFiber n, a (p.1 + 1) = ∑ p ∈ n.divisorsAntidiagonal, a p.1 := by
    refine Finset.sum_nbij' (fun p : ℕ × ℕ => (p.1 + 1, p.2 + 1))
      (fun x : ℕ × ℕ => (x.1 - 1, x.2 - 1)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ hp
      have hmul : (i + 1) * (j + 1) = n := mem_lambertFiber.mp hp
      refine Nat.mem_divisorsAntidiagonal.mpr ⟨hmul, ?_⟩
      rw [← hmul]
      exact mul_ne_zero (by omega) (by omega)
    · rintro ⟨u, v⟩ hx
      have hmul : u * v = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have h1 : u ≠ 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx
      have h2 : v ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx
      have e1 : u - 1 + 1 = u := by omega
      have e2 : v - 1 + 1 = v := by omega
      refine mem_lambertFiber.mpr ?_
      show (u - 1 + 1) * (v - 1 + 1) = n
      rw [e1, e2]
      exact hmul
    · rintro ⟨i, j⟩ _
      show ((i + 1 - 1 : ℕ), (j + 1 - 1 : ℕ)) = ((i : ℕ), (j : ℕ))
      simp
    · rintro ⟨u, v⟩ hx
      have h1 : u ≠ 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx
      have h2 : v ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx
      have e1 : u - 1 + 1 = u := by omega
      have e2 : v - 1 + 1 = v := by omega
      show ((u - 1 + 1 : ℕ), (v - 1 + 1 : ℕ)) = ((u : ℕ), (v : ℕ))
      rw [e1, e2]
    · rintro ⟨i, j⟩ _
      rfl
  rw [key]
  exact Nat.sum_divisorsAntidiagonal (fun x _ => a x)

/-- The double family `(i, j) ↦ a_{i+1} q^{(i+1)(j+1)}` is absolutely summable for `‖q‖ < 1`
whenever the coefficients are bounded, because `(i+1)(j+1) ≥ i + (j+1)`. -/
theorem summable_lambertPairs {a : ℕ → 𝕜} {C : ℝ} (hC : ∀ n, ‖a n‖ ≤ C) {q : 𝕜}
    (hq : ‖q‖ < 1) :
    Summable fun p : ℕ × ℕ => a (p.1 + 1) * q ^ ((p.1 + 1) * (p.2 + 1)) := by
  have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (a 0)) (hC 0)
  have hg1 : Summable fun i : ℕ => C * ‖q‖ ^ i :=
    (summable_geometric_of_lt_one hq0 hq).mul_left C
  have hg2 : Summable fun j : ℕ => ‖q‖ ^ (j + 1) :=
    (summable_nat_add_iff (f := fun i : ℕ => ‖q‖ ^ i) 1).mpr
      (summable_geometric_of_lt_one hq0 hq)
  have hprod := hg1.mul_of_nonneg hg2 (fun i => mul_nonneg hC0 (pow_nonneg hq0 i))
    (fun j => pow_nonneg hq0 (j + 1))
  refine Summable.of_norm_bounded hprod ?_
  rintro ⟨i, j⟩
  have hle : i + (j + 1) ≤ (i + 1) * (j + 1) := by
    have hexp : (i + 1) * (j + 1) = i * j + (i + (j + 1)) := by ring
    rw [hexp]
    exact Nat.le_add_left _ _
  calc ‖a (i + 1) * q ^ ((i + 1) * (j + 1))‖
      = ‖a (i + 1)‖ * ‖q‖ ^ ((i + 1) * (j + 1)) := by rw [norm_mul, norm_pow]
    _ ≤ C * ‖q‖ ^ (i + (j + 1)) :=
        mul_le_mul (hC _) (pow_le_pow_of_le_one hq0 hq.le hle) (pow_nonneg hq0 _) hC0
    _ = C * ‖q‖ ^ i * ‖q‖ ^ (j + 1) := by rw [pow_add, mul_assoc]

/-- **The Lambert series of an arbitrary bounded coefficient sequence**: for `‖q‖ < 1`,
`∑_{n ≥ 0} (∑_{d ∣ n} a_d) q^n = ∑'_d a_d q^d/(1 - q^d)`.  This is the rearrangement that the
proof of `qg:cor-two-square-lambert` performs without comment; it holds over an arbitrary
complete normed field and for any coefficients with `‖a n‖ ≤ C`.  The `d = 0` term of the
right-hand side is `a 0 · q⁰/(1 - q⁰) = a 0 / 0 = 0`, and `Nat.divisors 0 = ∅`, so the
`ℕ`-indexing is harmless. -/
theorem hasSum_lambert {a : ℕ → 𝕜} {C : ℝ} (hC : ∀ n, ‖a n‖ ≤ C) {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (∑ d ∈ n.divisors, a d) * q ^ n)
      (∑' d : ℕ, a d * q ^ d / (1 - q ^ d)) := by
  have hFS : HasSum (fun p : ℕ × ℕ => a (p.1 + 1) * q ^ ((p.1 + 1) * (p.2 + 1)))
      (∑' p : ℕ × ℕ, a (p.1 + 1) * q ^ ((p.1 + 1) * (p.2 + 1))) :=
    (summable_lambertPairs hC hq).hasSum
  -- Regroup the double family along the fibres of `(i, j) ↦ (i+1)(j+1)`.
  have hcoef : ∀ n : ℕ,
      (∑ p ∈ lambertFiber n, a (p.1 + 1) * q ^ ((p.1 + 1) * (p.2 + 1)))
        = (∑ d ∈ n.divisors, a d) * q ^ n := by
    intro n
    have h1 : ∀ p ∈ lambertFiber n,
        a (p.1 + 1) * q ^ ((p.1 + 1) * (p.2 + 1)) = a (p.1 + 1) * q ^ n := by
      intro p hp
      rw [mem_lambertFiber.mp hp]
    have h2 : ∑ p ∈ lambertFiber n, a (p.1 + 1) * q ^ ((p.1 + 1) * (p.2 + 1))
        = ∑ p ∈ lambertFiber n, a (p.1 + 1) * q ^ n := Finset.sum_congr rfl h1
    rw [h2, ← Finset.sum_mul (lambertFiber n) (fun p : ℕ × ℕ => a (p.1 + 1)) (q ^ n),
      sum_lambertFiber]
  have hregroup := hasSum_regroup hFS (fun p : ℕ × ℕ => (p.1 + 1) * (p.2 + 1)) lambertFiber
    (fun n p => mem_lambertFiber)
  have hmain : HasSum (fun n : ℕ => (∑ d ∈ n.divisors, a d) * q ^ n)
      (∑' p : ℕ × ℕ, a (p.1 + 1) * q ^ ((p.1 + 1) * (p.2 + 1))) := by
    refine hregroup.congr_fun fun n => ?_
    exact (hcoef n).symm
  -- Sum the same family fibrewise in the first variable, by geometric series.
  have hfib : ∀ b : ℕ, HasSum (fun c : ℕ => a (b + 1) * q ^ ((b + 1) * (c + 1)))
      (a (b + 1) * q ^ (b + 1) / (1 - q ^ (b + 1))) := by
    intro b
    have hr : ‖q ^ (b + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero b)
    have h0 : HasSum (fun c : ℕ => q ^ (b + 1) * (q ^ (b + 1)) ^ c)
        (q ^ (b + 1) * (1 - q ^ (b + 1))⁻¹) :=
      (hasSum_geometric_of_norm_lt_one hr).mul_left _
    have h1 : HasSum (fun c : ℕ => q ^ ((b + 1) * (c + 1)))
        (q ^ (b + 1) * (1 - q ^ (b + 1))⁻¹) := by
      refine h0.congr_fun fun c => ?_
      have hexp : (b + 1) * (c + 1) = (b + 1) + (b + 1) * c := by ring
      rw [hexp, pow_add, pow_mul]
    have h2 := h1.mul_left (a (b + 1))
    have heq : a (b + 1) * (q ^ (b + 1) * (1 - q ^ (b + 1))⁻¹)
        = a (b + 1) * q ^ (b + 1) / (1 - q ^ (b + 1)) := by
      rw [div_eq_mul_inv, mul_assoc]
    rw [heq] at h2
    exact h2
  have htotal := hFS.prod_fiberwise
    (g := fun b : ℕ => a (b + 1) * q ^ (b + 1) / (1 - q ^ (b + 1))) hfib
  -- Restore the `d`-indexing; the `d = 0` term vanishes.
  have hshift : HasSum (fun d : ℕ => a d * q ^ d / (1 - q ^ d))
      (∑' p : ℕ × ℕ, a (p.1 + 1) * q ^ ((p.1 + 1) * (p.2 + 1))) := by
    have h2 := (hasSum_nat_add_iff (f := fun d : ℕ => a d * q ^ d / (1 - q ^ d)) 1).mp htotal
    simp only [Finset.sum_range_one, pow_zero, mul_one, sub_self, div_zero, add_zero] at h2
    exact h2
  rw [hshift.tsum_eq]
  exact hmain

/-- **The Lambert series of `χ₄`**: `∑_{n ≥ 0} D(n) q^n = ∑'_d χ₄(d) q^d/(1 - q^d)` for
`‖q‖ < 1`.  This is the first Lambert series of `eq:qg-two-square-lambert`, expanded into a
power series — the step the printed proof asserts without justifying the rearrangement. -/
theorem hasSum_twoSquareDivisorSum_lambert {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => ((twoSquareDivisorSum n : ℤ) : 𝕜) * q ^ n)
      (∑' d : ℕ, ((chi4 d : ℤ) : 𝕜) * q ^ d / (1 - q ^ d)) := by
  have h := hasSum_lambert (a := fun d : ℕ => ((chi4 d : ℤ) : 𝕜)) (C := 1)
    (fun n => norm_intCast_chi4_le_one n) hq
  refine h.congr_fun fun n => ?_
  have hs : ((twoSquareDivisorSum n : ℤ) : 𝕜) = ∑ d ∈ n.divisors, ((chi4 d : ℤ) : 𝕜) := by
    unfold twoSquareDivisorSum
    exact Int.cast_sum _ _
  rw [hs]

omit [CompleteSpace 𝕜] in
/-- **The second equality of `eq:qg-two-square-lambert`**, unconditionally:
`∑'_d χ₄(d) q^d/(1 - q^d) = ∑'_j (-1)^j q^{2j+1}/(1 - q^{2j+1})`.  No convergence hypothesis is
needed, and completeness is not used: `χ₄` vanishes on even arguments, so the support of the
left family lies in the odd numbers, and `χ₄(2j+1) = (-1)^j`. -/
theorem tsum_chi4_lambert_eq_tsum_odd {q : 𝕜} :
    ∑' d : ℕ, ((chi4 d : ℤ) : 𝕜) * q ^ d / (1 - q ^ d)
      = ∑' j : ℕ, (-1 : 𝕜) ^ j * q ^ (2 * j + 1) / (1 - q ^ (2 * j + 1)) := by
  have hginj : Function.Injective (fun j : ℕ => 2 * j + 1) := by
    intro x y hxy
    have hxy' : 2 * x + 1 = 2 * y + 1 := hxy
    omega
  have hsupp : Function.support (fun d : ℕ => ((chi4 d : ℤ) : 𝕜) * q ^ d / (1 - q ^ d))
      ⊆ Set.range (fun j : ℕ => 2 * j + 1) := by
    intro d hd
    have hne : ((chi4 d : ℤ) : 𝕜) * q ^ d / (1 - q ^ d) ≠ 0 := hd
    have hodd : d % 2 = 1 := by
      by_contra hcon
      have h0 : d % 2 = 0 := by omega
      have hzero : ((chi4 d : ℤ) : 𝕜) * q ^ d / (1 - q ^ d) = 0 := by
        rw [chi4_of_even h0]
        simp
      exact hne hzero
    have hd2 : 2 * (d / 2) + 1 = d := by omega
    exact ⟨d / 2, hd2⟩
  have hmove := hginj.tsum_eq
    (f := fun d : ℕ => ((chi4 d : ℤ) : 𝕜) * q ^ d / (1 - q ^ d)) hsupp
  refine hmove.symm.trans ?_
  refine tsum_congr fun j => ?_
  have hcast : (((-1 : ℤ) ^ j : ℤ) : 𝕜) = (-1 : 𝕜) ^ j := by
    rw [Int.cast_pow, Int.cast_neg, Int.cast_one]
  show ((chi4 (2 * j + 1) : ℤ) : 𝕜) * q ^ (2 * j + 1) / (1 - q ^ (2 * j + 1))
      = (-1 : 𝕜) ^ j * q ^ (2 * j + 1) / (1 - q ^ (2 * j + 1))
  rw [chi4_two_mul_add_one, hcast]

/-! ## The corollary, reduced to the arithmetic core -/

/-- **`qg:cor-two-square-lambert`, first equality**, granted the counting formula
`eq:qg-two-square`: for `‖q‖ < 1`,
`(∑_{m ∈ ℤ} q^{m²})² = 1 + 4 ∑'_d χ₄(d) q^d/(1 - q^d)`.

The hypothesis `h` is exactly the arithmetic core of `qg:thm-two-square` that this module does
not prove (see the module docstring).  Everything analytic — the theta expansion
`qg:prop-squares-theta`, the Lambert rearrangement, and the separate `n = 0` term
`r₂(0) = 1` — is discharged here. -/
theorem hasSum_theta_sq_lambert
    (h : ∀ n : ℕ, n ≠ 0 → (sumSqRep 2 n : ℤ) = 4 * twoSquareDivisorSum n)
    {q : 𝕜} (hq : ‖q‖ < 1) :
    (∑' m : ℤ, q ^ (m.natAbs ^ 2)) ^ 2
      = 1 + 4 * ∑' d : ℕ, ((chi4 d : ℤ) : 𝕜) * q ^ d / (1 - q ^ d) := by
  have h4 : HasSum (fun n : ℕ => (4 : 𝕜) * (((twoSquareDivisorSum n : ℤ) : 𝕜) * q ^ n))
      (4 * ∑' d : ℕ, ((chi4 d : ℤ) : 𝕜) * q ^ d / (1 - q ^ d)) :=
    (hasSum_twoSquareDivisorSum_lambert hq).mul_left 4
  have hsum := h4.add (hasSum_ite_eq (0 : ℕ) (1 : 𝕜))
  have hcongr : HasSum (fun n : ℕ => (sumSqRep 2 n : 𝕜) * q ^ n)
      (4 * (∑' d : ℕ, ((chi4 d : ℤ) : 𝕜) * q ^ d / (1 - q ^ d)) + 1) := by
    refine hsum.congr_fun fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [sumSqRep_two_zero, twoSquareDivisorSum_zero]
    · have hcast : ((sumSqRep 2 n : ℕ) : 𝕜) = 4 * ((twoSquareDivisorSum n : ℤ) : 𝕜) := by
        have h1 : ((sumSqRep 2 n : ℤ) : 𝕜) = ((4 * twoSquareDivisorSum n : ℤ) : 𝕜) := by
          rw [h n hn]
        rw [Int.cast_natCast, Int.cast_mul] at h1
        have h4' : ((4 : ℤ) : 𝕜) = 4 := by norm_num
        rw [h4'] at h1
        exact h1
      simp only [hcast, if_neg hn]
      ring
  have huniq := (hasSum_sumSqRep hq 2).unique hcongr
  rw [huniq]
  ring

/-- **`qg:cor-two-square-lambert` in full**, granted the counting formula `eq:qg-two-square`:
both displayed equalities of `eq:qg-two-square-lambert` at once. -/
theorem theta_sq_eq_lambert_odd
    (h : ∀ n : ℕ, n ≠ 0 → (sumSqRep 2 n : ℤ) = 4 * twoSquareDivisorSum n)
    {q : 𝕜} (hq : ‖q‖ < 1) :
    (∑' m : ℤ, q ^ (m.natAbs ^ 2)) ^ 2
      = 1 + 4 * ∑' j : ℕ, (-1 : 𝕜) ^ j * q ^ (2 * j + 1) / (1 - q ^ (2 * j + 1)) := by
  rw [hasSum_theta_sq_lambert h hq, tsum_chi4_lambert_eq_tsum_odd]

end Lambert

end Fabius
