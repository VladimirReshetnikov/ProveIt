import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

/-!
# The quadratic core, and its Catalan coefficients

The transseries volume's `p6:lem:quadratic-core` isolates the *quadratic model*

`A ε + c ε² + σ q = 0`

as the common core of the deepest-pole families of several special-function
inversions.  Its unique solution of positive valuation is

`ε = (A / 2c) (√(1 - 4cσq/A²) - 1)`,
`ε_n = ((-4cσ)^n / 2c) · binom(1/2, n) · A^{-(2n-1)}`,

and `p6:thm:deepest-pole` reads both the Gamma and the Barnes `G` deepest-pole
coefficients off it, under the dictionary `(A,c,σ) = (Λ, 1/2, a₁)` and
`(A,c,σ) = (2λ, 1, 2α)`.

The volume states this analytically, through the binomial series for `√(1+w)`.
It is in fact pure algebra, and it has a shortcut the volume does not record:

`binom(1/2, n) = (-1)^{n-1} · catalan (n-1) / 2^{2n-1}`,

so the convolution that the quadratic model demands of its coefficients,

`∑_{j=1}^{n-1} binom(1/2,j) binom(1/2,n-j) = -2 · binom(1/2,n)`,

is *literally* the Catalan recursion `catalan_succ'` over `Finset.antidiagonal`.
No power series, no binomial series, and no induction on the convolution: the
identity `(1+w)^{1/2} · (1+w)^{1/2} = 1+w` is replaced by the combinatorial
recursion that already lives in Mathlib.

Everything here is over an arbitrary field of characteristic zero, and the
module is a Mathlib-only leaf: it imports nothing from the rest of the corpus.

## Main results

* `catalan_two_step`: `(n+2) · catalan (n+1) = 2(2n+1) · catalan n`, the ratio
  recursion, deduced from the central binomial recursion.
* `quadHalf`: the coefficient family, indexed so that `quadHalf K n` is
  `binom(1/2, n+1)`; defined by the Catalan closed form, so that closed form is
  true by definition.
* `quadHalf_antidiagonal`: the convolution `∑ = -2 · quadHalf K (m+1)`.
* `quadHalf_rat`: the bridge to the volume's own notation — over `ℚ` this family
  *is* the generalized binomial coefficient `binom(1/2, n+1)`.
* `quadCoef_zero` and `quadCoef_rec`: the coefficients
  `ε_{n+1} = ((-4cσ)^{n+1}/2c) · binom(1/2,n+1) · A^{-(2n+1)}` satisfy the
  recursion defining the quadratic model, which is the content of
  `p6:lem:quadratic-core`.

What is *not* formalized here: that these coefficients are the deepest-pole
coefficients of the Gamma and Barnes `G` inversions.  That identification is
`p6:thm:deepest-pole` and needs the transseries apparatus; this module supplies
only the algebraic core it reduces to.
-/

set_option autoImplicit false

namespace Fabius

open Finset

/-- The two-step ratio recursion for the Catalan numbers,
`(n+2) · catalan (n+1) = 2(2n+1) · catalan n`, obtained by cancelling `n+1`
from the central binomial recursion. -/
theorem catalan_two_step (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have hA : (n + 2) * catalan (n + 1) = Nat.centralBinom (n + 1) :=
    succ_mul_catalan_eq_centralBinom (n + 1)
  have hB : (n + 1) * catalan n = Nat.centralBinom n := succ_mul_catalan_eq_centralBinom n
  have h : (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * (2 * (2 * n + 1) * catalan n) := by
    rw [hA, Nat.succ_mul_centralBinom_succ n, ← hB]
    ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) h

/-- The coefficient family of the quadratic model, indexed from zero:
`quadHalf K n = (-1)^n · catalan n / 2^{2n+1}`, which is `binom(1/2, n+1)`
(see `quadHalf_rat`). -/
noncomputable def quadHalf (K : Type*) [Field K] (n : ℕ) : K :=
  (-1) ^ n * (catalan n : K) / 2 ^ (2 * n + 1)

variable {K : Type*} [Field K] [CharZero K]

theorem quadHalf_zero : quadHalf K 0 = 1 / 2 := by
  rw [quadHalf]
  norm_num

/-- The convolution identity behind the quadratic model.  Under the Catalan
closed form it is exactly `catalan_succ'`. -/
theorem quadHalf_antidiagonal (m : ℕ) :
    ∑ p ∈ Finset.antidiagonal m, quadHalf K p.1 * quadHalf K p.2
      = -2 * quadHalf K (m + 1) := by
  have hterm : ∀ p ∈ Finset.antidiagonal m,
      quadHalf K p.1 * quadHalf K p.2
        = (-1) ^ m / 2 ^ (2 * m + 2) * ((catalan p.1 : K) * (catalan p.2 : K)) := by
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    have hd : (2 : K) ^ (2 * p.1 + 1) * 2 ^ (2 * p.2 + 1) = 2 ^ (2 * m + 2) := by
      rw [← pow_add]
      congr 1
      omega
    have hs : ((-1 : K)) ^ p.1 * (-1) ^ p.2 = (-1) ^ m := by
      rw [← pow_add, hp]
    simp only [quadHalf]
    calc (-1 : K) ^ p.1 * (catalan p.1 : K) / 2 ^ (2 * p.1 + 1)
            * ((-1) ^ p.2 * (catalan p.2 : K) / 2 ^ (2 * p.2 + 1))
        = ((-1 : K) ^ p.1 * (-1) ^ p.2) * ((catalan p.1 : K) * (catalan p.2 : K))
            / (2 ^ (2 * p.1 + 1) * 2 ^ (2 * p.2 + 1)) := by ring
      _ = (-1 : K) ^ m / 2 ^ (2 * m + 2) * ((catalan p.1 : K) * (catalan p.2 : K)) := by
          rw [hs, hd]
          ring
  have hcat : ∑ p ∈ Finset.antidiagonal m, ((catalan p.1 : K) * (catalan p.2 : K))
      = (catalan (m + 1) : K) := by
    rw [catalan_succ' m, Nat.cast_sum]
    exact Finset.sum_congr rfl fun p _ => (Nat.cast_mul _ _).symm
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hcat]
  simp only [quadHalf]
  rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 from by ring, pow_succ]
  have hp2 : (2 : K) ^ (2 * m + 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

/-- `halfBinom n` is the generalized binomial coefficient `binom(1/2, n)`, the
notation the volume uses. -/
noncomputable def halfBinom (n : ℕ) : ℚ :=
  (∏ i ∈ Finset.range n, ((1 : ℚ) / 2 - i)) / (Nat.factorial n)

theorem halfBinom_step (n : ℕ) :
    2 * ((n : ℚ) + 1) * halfBinom (n + 1) = (1 - 2 * n) * halfBinom n := by
  have hf : ((Nat.factorial n : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  simp only [halfBinom, Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  field_simp

/-- The bridge to the volume's notation: the Catalan family is the generalized
binomial coefficient `binom(1/2, n+1)`. -/
theorem quadHalf_rat (n : ℕ) : quadHalf ℚ n = halfBinom (n + 1) := by
  induction n with
  | zero =>
      rw [quadHalf_zero, halfBinom]
      norm_num
  | succ n ih =>
      have hn2 : ((n : ℚ) + 2) ≠ 0 := by positivity
      have hcat : ((n : ℚ) + 2) * (catalan (n + 1) : ℚ)
          = 2 * (2 * (n : ℚ) + 1) * (catalan n : ℚ) := by
        exact_mod_cast catalan_two_step n
      have h2 : (2 : ℚ) ^ (2 * (n + 1) + 1) = 2 ^ (2 * n + 1) * 4 := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 from by ring, pow_add]
        norm_num
      have hpow : (2 : ℚ) ^ (2 * n + 1) ≠ 0 := by positivity
      have hL : ((n : ℚ) + 2) * quadHalf ℚ (n + 1)
          = -(2 * (n : ℚ) + 1) * quadHalf ℚ n / 2 := by
        simp only [quadHalf]
        calc ((n : ℚ) + 2) * ((-1) ^ (n + 1) * (catalan (n + 1) : ℚ) / 2 ^ (2 * (n + 1) + 1))
            = (-1) ^ (n + 1) * (((n : ℚ) + 2) * (catalan (n + 1) : ℚ))
                / 2 ^ (2 * (n + 1) + 1) := by ring
          _ = (-1) ^ (n + 1) * (2 * (2 * (n : ℚ) + 1) * (catalan n : ℚ))
                / 2 ^ (2 * (n + 1) + 1) := by rw [hcat]
          _ = (-1) ^ (n + 1) * (2 * (2 * (n : ℚ) + 1) * (catalan n : ℚ))
                / (2 ^ (2 * n + 1) * 4) := by rw [h2]
          _ = -(2 * (n : ℚ) + 1) * ((-1) ^ n * (catalan n : ℚ) / 2 ^ (2 * n + 1)) / 2 := by
              field_simp
              ring
      have hR : ((n : ℚ) + 2) * halfBinom (n + 1 + 1)
          = -(2 * (n : ℚ) + 1) * halfBinom (n + 1) / 2 := by
        have hstep := halfBinom_step (n + 1)
        push_cast at hstep
        linear_combination hstep / 2
      refine mul_left_cancel₀ hn2 ?_
      rw [hL, hR, ih]

/-- The coefficients of the quadratic model, indexed from zero:
`quadCoef A c σ n` is the volume's `ε_{n+1}`. -/
noncomputable def quadCoef (A c σ : K) (n : ℕ) : K :=
  (-4 * c * σ) ^ (n + 1) / (2 * c) * quadHalf K n / A ^ (2 * n + 1)

/-- Over `ℚ` this is the volume's closed form
`ε_n = ((-4cσ)^n / 2c) · binom(1/2,n) · A^{-(2n-1)}`. -/
theorem quadCoef_rat (A c σ : ℚ) (n : ℕ) :
    quadCoef A c σ n
      = (-4 * c * σ) ^ (n + 1) / (2 * c) * halfBinom (n + 1) / A ^ (2 * n + 1) := by
  rw [quadCoef, quadHalf_rat]

/-- The order-one equation of the quadratic model: `A ε₁ + σ = 0`. -/
theorem quadCoef_zero (A c σ : K) (hA : A ≠ 0) (hc : c ≠ 0) :
    A * quadCoef A c σ 0 + σ = 0 := by
  simp only [quadCoef, quadHalf, catalan_zero, Nat.cast_one, pow_zero, Nat.mul_zero,
    Nat.zero_add, pow_one]
  field_simp
  ring

/-- The recursion of the quadratic model at every order beyond the first:
`A ε_n + c ∑_{j+k=n} ε_j ε_k = 0`.  Together with `quadCoef_zero` this is
`p6:lem:quadratic-core`. -/
theorem quadCoef_rec (A c σ : K) (hA : A ≠ 0) (hc : c ≠ 0) (m : ℕ) :
    A * quadCoef A c σ (m + 1)
      + c * ∑ p ∈ Finset.antidiagonal m, quadCoef A c σ p.1 * quadCoef A c σ p.2 = 0 := by
  have hP : A ^ (2 * m + 2) ≠ 0 := pow_ne_zero _ hA
  have hterm : ∀ p ∈ Finset.antidiagonal m,
      quadCoef A c σ p.1 * quadCoef A c σ p.2
        = (-4 * c * σ) ^ (m + 1 + 1) / (4 * c ^ 2 * A ^ (2 * m + 2))
            * (quadHalf K p.1 * quadHalf K p.2) := by
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    have hS : (-4 * c * σ) ^ (p.1 + 1) * (-4 * c * σ) ^ (p.2 + 1)
        = (-4 * c * σ) ^ (m + 1 + 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hAp : A ^ (2 * p.1 + 1) * A ^ (2 * p.2 + 1) = A ^ (2 * m + 2) := by
      rw [← pow_add]
      congr 1
      omega
    simp only [quadCoef]
    rw [← hS, ← hAp]
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, quadHalf_antidiagonal]
  simp only [quadCoef]
  have hAe : A ^ (2 * (m + 1) + 1) = A ^ (2 * m + 2) * A := by
    rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 from by ring, pow_succ]
  rw [hAe]
  field_simp
  ring

end Fabius
