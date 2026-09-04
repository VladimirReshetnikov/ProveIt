import FabiusFunction.HalfQBinomial
import FabiusFunction.QPochhammerDerivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Simplicity of the half-base q-binomial roots

The finite q-binomial theorem identifies

`sum k, (-1)^k (1/2)^(k.choose 2) * halfQBinomial n k * z^k`

with the finite product `(z; 1/2)_n`.  `HalfQBinomial` already classifies its
rational zeros as the dyadic points `2^j`, for `j < n`.  This leaf supplies
the complementary multiplicity statement: every one of those roots is
simple.

The proof differentiates the finite product.  At `z = 2^j`, every summand in
the product-rule formula vanishes except the one obtained by deleting the
`j`th factor, and all factors in that remaining product are nonzero.  Thus
the derivative does not vanish, so the root has multiplicity one.

## Main declaration

* `halfQBinomial_sum_rootMultiplicity_two_pow` -- every dyadic root in the
  complete half-base root locus has multiplicity exactly one.

The result is stated over `ℚ`, matching the exact rational half-q-binomial
API.  Together with `halfQBinomial_sum_eq_zero_iff` and
`gaussianBinomial_half_eq_halfQBinomial`, it gives the simple-root statement
for the manuscript's Gaussian-binomial polynomial at `q = 1/2`.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

private theorem one_sub_two_pow_mul_half_pow_ne_zero
    (i j : ℕ) (hij : i ≠ j) :
    1 - (2 : ℚ) ^ j * (1 / 2 : ℚ) ^ i ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have hpow : (2 : ℚ) ^ i = (2 : ℚ) ^ j := by
    calc
      (2 : ℚ) ^ i = 1 * (2 : ℚ) ^ i := by rw [one_mul]
      _ = ((2 : ℚ) ^ j * (1 / 2 : ℚ) ^ i) * (2 : ℚ) ^ i := by rw [← h]
      _ = (2 : ℚ) ^ j := by
        rw [mul_assoc, ← mul_pow]
        norm_num
  exact hij (pow_right_injective₀ (a := (2 : ℚ)) (by norm_num) (by norm_num) hpow)

/-- Every root `2^j`, `j < n`, of the half-base q-binomial polynomial is
simple.  The polynomial is written coefficientwise so the theorem composes
directly with the existing complete rational root classification
`halfQBinomial_sum_eq_zero_iff`. -/
theorem halfQBinomial_sum_rootMultiplicity_two_pow
    (n j : ℕ) (hj : j < n) :
    (∑ k ∈ Finset.range (n + 1),
      Polynomial.monomial k
        ((-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
          halfQBinomial n k)).rootMultiplicity ((2 : ℚ) ^ j) = 1 := by
  let p : Polynomial ℚ :=
    ∑ k ∈ Finset.range (n + 1),
      Polynomial.monomial k
        ((-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
          halfQBinomial n k)
  have hp_eval (z : ℚ) :
      p.eval z =
        ∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
            halfQBinomial n k * z ^ k := by
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  have hp_fun :
      (fun z : ℚ => p.eval z) =
        fun z : ℚ => finiteQPochhammerIn z (1 / 2) n := by
    funext z
    rw [hp_eval]
    simpa only [finiteQPochhammerIn_rat_eq] using
      halfQBinomial_theorem n z
  have hjmem : j ∈ Finset.range n := Finset.mem_range.mpr hj
  have hsum :
      (∑ r ∈ Finset.range n,
        (1 / 2 : ℚ) ^ r *
          ∏ i ∈ (Finset.range n).erase r,
            (1 - (2 : ℚ) ^ j * (1 / 2 : ℚ) ^ i)) =
        (1 / 2 : ℚ) ^ j *
          ∏ i ∈ (Finset.range n).erase j,
            (1 - (2 : ℚ) ^ j * (1 / 2 : ℚ) ^ i) := by
    apply Finset.sum_eq_single j
    · intro r hr hrj
      have hj_erase : j ∈ (Finset.range n).erase r :=
        Finset.mem_erase.mpr ⟨Ne.symm hrj, hjmem⟩
      have hzero :
          ∏ i ∈ (Finset.range n).erase r,
              (1 - (2 : ℚ) ^ j * (1 / 2 : ℚ) ^ i) = 0 := by
        apply Finset.prod_eq_zero (i := j)
        · exact hj_erase
        · rw [← mul_pow]
          norm_num
      rw [hzero, mul_zero]
    · exact fun hnot => (hnot hjmem).elim
  have hproduct_ne :
      (∏ i ∈ (Finset.range n).erase j,
        (1 - (2 : ℚ) ^ j * (1 / 2 : ℚ) ^ i)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    exact one_sub_two_pow_mul_half_pow_ne_zero i j
      (Finset.ne_of_mem_erase hi)
  have hterm_ne :
      (1 / 2 : ℚ) ^ j *
          ∏ i ∈ (Finset.range n).erase j,
            (1 - (2 : ℚ) ^ j * (1 / 2 : ℚ) ^ i) ≠ 0 :=
    mul_ne_zero (pow_ne_zero j (by norm_num)) hproduct_ne
  have hderiv_eval :
      p.derivative.eval ((2 : ℚ) ^ j) =
        -(∑ r ∈ Finset.range n,
          (1 / 2 : ℚ) ^ r *
            ∏ i ∈ (Finset.range n).erase r,
              (1 - (2 : ℚ) ^ j * (1 / 2 : ℚ) ^ i)) := by
    calc
      p.derivative.eval ((2 : ℚ) ^ j) =
          deriv (fun z : ℚ => p.eval z) ((2 : ℚ) ^ j) := p.deriv.symm
      _ = deriv (fun z : ℚ => finiteQPochhammerIn z (1 / 2) n)
          ((2 : ℚ) ^ j) := by rw [hp_fun]
      _ = _ :=
        (hasDerivAt_finiteQPochhammerIn (1 / 2 : ℚ) n
          ((2 : ℚ) ^ j)).deriv
  have hderiv_ne : p.derivative.eval ((2 : ℚ) ^ j) ≠ 0 := by
    rw [hderiv_eval, hsum]
    exact neg_ne_zero.mpr hterm_ne
  have hp : p ≠ 0 := by
    intro hp
    rw [hp] at hderiv_ne
    simp at hderiv_ne
  have hroot : p.IsRoot ((2 : ℚ) ^ j) := by
    rw [Polynomial.IsRoot, hp_eval]
    exact (halfQBinomial_sum_eq_zero_iff n ((2 : ℚ) ^ j)).2
      ⟨j, hj, rfl⟩
  have hpos : 0 < p.rootMultiplicity ((2 : ℚ) ^ j) :=
    (Polynomial.rootMultiplicity_pos hp).2 hroot
  have hnot : ¬ 1 < p.rootMultiplicity ((2 : ℚ) ^ j) := by
    intro hlt
    have hroots :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).1 hlt
    exact hderiv_ne hroots.2.eq_zero
  change p.rootMultiplicity ((2 : ℚ) ^ j) = 1
  omega

end Fabius
