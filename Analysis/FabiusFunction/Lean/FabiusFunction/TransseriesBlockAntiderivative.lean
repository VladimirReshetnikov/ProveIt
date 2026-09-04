import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Block antidifferentiation and the resonant block

The transseries volume's `plt:lem:mot-block-antiderivative`.  In the
polynomial–logarithmic ring `K[t,t⁻¹][L]` the derivation acts inside a
fixed power of `t` as the `K`-linear operator

`∂_L - c`   on `K[L]`,

where `c` is the outer exponent of the block.  The lemma says the
operator is a degree-preserving bijection when `c ≠ 0`, while at the
*resonant* block `c = 0` it degenerates to `∂_L`, which is surjective
with kernel the constants and raises degree by one.  That dichotomy is
why antidifferentiation creates a logarithm at exactly one level.

Everything here is about `Polynomial K`; only the resonant half needs
characteristic zero.

* `sum_sub_sum_shift` — the telescoping identity behind the inverse.
* `blockOperator c p = ∂p - c·p`, over any commutative ring.
* `blockAntiderivative` — an **explicit finite inverse**
  `-∑_{k≤deg f} c^{-(k+1)}·∂^k f`, the Neumann series of `∂/c`, finite
  because `∂` is nilpotent on polynomials of bounded degree.
* `blockOperator_blockAntiderivative` — it *is* an inverse, hence
  `blockOperator_surjective`.
* `blockOperator_injective`, `blockOperator_bijective`,
  `natDegree_blockOperator` — the nonresonant case `c ≠ 0`.
* `resonantAntiderivative`, `derivative_resonantAntiderivative`,
  `derivative_surjective` — the resonant case: over a characteristic-zero
  field every polynomial is a derivative, with an explicit primitive.
* `natDegree_resonantAntiderivative` — and it raises degree by one.
-/

set_option autoImplicit false

open Polynomial Finset

namespace Fabius

/-- **Telescoping of a shifted sum**: `∑_{k≤n} g k - ∑_{k≤n} g (k+1) =
g 0 - g (n+1)` in any additive commutative group. -/
theorem sum_sub_sum_shift {M : Type*} [AddCommGroup M] (g : ℕ → M) (n : ℕ) :
    ∑ k ∈ range (n + 1), g k - ∑ k ∈ range (n + 1), g (k + 1) =
      g 0 - g (n + 1) := by
  rw [Finset.sum_range_succ' g n, Finset.sum_range_succ (fun k => g (k + 1)) n]
  abel

/-- The block operator `∂_L - c` acting on the logarithmic polynomial
ring of a single block.  Only a commutative ring is needed to state it;
the inversion results below need a field. -/
noncomputable def blockOperator {R : Type*} [CommRing R] (c : R)
    (p : R[X]) : R[X] :=
  derivative p - Polynomial.C c * p

/-- The block operator sends the zero polynomial to zero. -/
@[simp] theorem blockOperator_zero {R : Type*} [CommRing R] (c : R) :
    blockOperator c 0 = 0 := by
  simp [blockOperator]

/-- The block operator is additive in its polynomial argument. -/
theorem blockOperator_sub {R : Type*} [CommRing R] (c : R) (p q : R[X]) :
    blockOperator c (p - q) = blockOperator c p - blockOperator c q := by
  simp only [blockOperator, map_sub, mul_sub]
  ring

variable {K : Type*} [Field K]

/-- The explicit inverse of `∂_L - c` at `c ≠ 0`: the finite Neumann sum
`-∑_{k ≤ deg f} c^{-(k+1)}·∂^k f`.  The sum is finite because `∂` kills
every polynomial after `deg f + 1` steps. -/
noncomputable def blockAntiderivative (c : K) (f : K[X]) : K[X] :=
  -∑ k ∈ range (f.natDegree + 1),
    Polynomial.C ((c ^ (k + 1))⁻¹) * (derivative^[k] f)

/-- **The block operator is inverted by the Neumann sum.**  With
`gₖ = c^{-k}·∂^k f` the two sums telescope to `g₀ - g_{deg f + 1}`, and
the second term vanishes because `∂^{deg f + 1} f = 0`. -/
theorem blockOperator_blockAntiderivative {c : K} (hc : c ≠ 0) (f : K[X]) :
    blockOperator c (blockAntiderivative c f) = f := by
  have hshift : ∀ k ∈ range (f.natDegree + 1),
      derivative (Polynomial.C ((c ^ (k + 1))⁻¹) * (derivative^[k] f)) =
        Polynomial.C ((c ^ (k + 1))⁻¹) * (derivative^[k + 1] f) := by
    intro k _
    rw [Polynomial.derivative_C_mul, Function.iterate_succ_apply']
  have hscale : ∀ k ∈ range (f.natDegree + 1),
      Polynomial.C c * (Polynomial.C ((c ^ (k + 1))⁻¹) * (derivative^[k] f)) =
        Polynomial.C ((c ^ k)⁻¹) * (derivative^[k] f) := by
    intro k _
    rw [← mul_assoc, ← map_mul]
    congr 2
    rw [pow_succ]
    field_simp
  have key := sum_sub_sum_shift
    (fun k => Polynomial.C ((c ^ k)⁻¹) * (derivative^[k] f)) f.natDegree
  simp only [pow_zero, inv_one, map_one, one_mul, Function.iterate_zero_apply,
    Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self f.natDegree),
    mul_zero, sub_zero] at key
  rw [blockOperator, blockAntiderivative, map_neg, map_sum, mul_neg,
    Finset.mul_sum, Finset.sum_congr rfl hshift, Finset.sum_congr rfl hscale]
  linear_combination key

/-- **Surjectivity** of `∂_L - c` for `c ≠ 0`. -/
theorem blockOperator_surjective {c : K} (hc : c ≠ 0) :
    Function.Surjective (blockOperator c) :=
  fun f => ⟨blockAntiderivative c f, blockOperator_blockAntiderivative hc f⟩

/-- The degree of `c·p` is the degree of `p` when `c ≠ 0`. -/
theorem natDegree_C_mul_of_ne_zero {c : K} (hc : c ≠ 0) (p : K[X]) :
    (Polynomial.C c * p).natDegree = p.natDegree := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [Polynomial.natDegree_mul (by simpa using hc) hp, Polynomial.natDegree_C,
      zero_add]

/-- **Degree preservation**: for `c ≠ 0` the block operator does not
change the logarithmic degree, because `∂p` has strictly smaller degree
than `c·p`. -/
theorem natDegree_blockOperator {c : K} (hc : c ≠ 0) (p : K[X]) :
    (blockOperator c p).natDegree = p.natDegree := by
  rcases eq_or_ne p.natDegree 0 with hd | hd
  · -- a constant block: `∂p = 0` and the operator is multiplication by `-c`
    rw [blockOperator, Polynomial.derivative_of_natDegree_zero hd, zero_sub,
      Polynomial.natDegree_neg, natDegree_C_mul_of_ne_zero hc]
  · have hlt : (derivative p).natDegree < (Polynomial.C c * p).natDegree := by
      rw [natDegree_C_mul_of_ne_zero hc]
      exact Polynomial.natDegree_derivative_lt hd
    rw [blockOperator, Polynomial.natDegree_sub_eq_right_of_natDegree_lt hlt,
      natDegree_C_mul_of_ne_zero hc]

/-- **Injectivity** of `∂_L - c` for `c ≠ 0`: a nonzero kernel element
would have to satisfy `∂p = c·p`, impossible by degree. -/
theorem blockOperator_injective {c : K} (hc : c ≠ 0) :
    Function.Injective (blockOperator c) := by
  intro p q hpq
  have hzero : blockOperator c (p - q) = 0 := by
    rw [blockOperator_sub, hpq, sub_self]
  by_contra hne
  have hd : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hdeg := natDegree_blockOperator hc (p - q)
  rw [hzero, Polynomial.natDegree_zero] at hdeg
  -- so `p - q` is a nonzero constant, and then the operator is `-c·(p-q)`
  rw [blockOperator, Polynomial.derivative_of_natDegree_zero hdeg.symm, zero_sub,
    neg_eq_zero] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · exact hc (by simpa using h)
  · exact hd h

/-- **The nonresonant block**: `∂_L - c` is a degree-preserving bijection
of `K[L]` for every `c ≠ 0`. -/
theorem blockOperator_bijective {c : K} (hc : c ≠ 0) :
    Function.Bijective (blockOperator c) :=
  ⟨blockOperator_injective hc, blockOperator_surjective hc⟩

/-! ## The resonant block `c = 0` -/

variable [CharZero K]

/-- The explicit antiderivative of a polynomial over a characteristic
zero field: integrate each monomial. -/
noncomputable def resonantAntiderivative (f : K[X]) : K[X] :=
  ∑ k ∈ range (f.natDegree + 1),
    Polynomial.C (f.coeff k / (k + 1)) * X ^ (k + 1)

/-- **The resonant block integrates**: `∂` applied to the explicit
antiderivative returns the polynomial. -/
theorem derivative_resonantAntiderivative (f : K[X]) :
    derivative (resonantAntiderivative f) = f := by
  rw [resonantAntiderivative, map_sum]
  have hterm : ∀ k ∈ range (f.natDegree + 1),
      derivative (Polynomial.C (f.coeff k / (k + 1)) * X ^ (k + 1)) =
        Polynomial.C (f.coeff k) * X ^ k := by
    intro k _
    have hk : ((k : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
    rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow,
      Nat.add_sub_cancel, ← mul_assoc, ← map_mul]
    congr 2
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hterm]
  exact (Polynomial.as_sum_range_C_mul_X_pow f).symm

/-- **Surjectivity at the resonant block**: over a characteristic zero
field every polynomial is a derivative.  This is the `c = 0` half of the
block lemma; with `Polynomial.derivative_eq_zero` (the kernel is the
constants) it says `∂` is surjective with one-dimensional kernel. -/
theorem derivative_surjective :
    Function.Surjective (derivative : K[X] → K[X]) :=
  fun f => ⟨resonantAntiderivative f, derivative_resonantAntiderivative f⟩

/-- **Antidifferentiation raises the logarithmic degree by one** at the
resonant block. -/
theorem natDegree_resonantAntiderivative (f : K[X]) (hf : f ≠ 0) :
    (resonantAntiderivative f).natDegree = f.natDegree + 1 := by
  have hd : derivative (resonantAntiderivative f) = f :=
    derivative_resonantAntiderivative f
  have hdeg : f.natDegree < (resonantAntiderivative f).natDegree := by
    rcases eq_or_ne (resonantAntiderivative f).natDegree 0 with h0 | h0
    · rw [Polynomial.derivative_of_natDegree_zero h0] at hd
      exact absurd hd.symm hf
    · have hlt := Polynomial.natDegree_derivative_lt h0
      rwa [hd] at hlt
  refine le_antisymm ?_ hdeg
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  calc (Polynomial.C (f.coeff k / (k + 1)) * X ^ (k + 1)).natDegree
      ≤ (Polynomial.C (f.coeff k / (k + 1))).natDegree +
          (X ^ (k + 1) : K[X]).natDegree := Polynomial.natDegree_mul_le
    _ ≤ f.natDegree + 1 := by
        rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]
        have := Finset.mem_range.mp hk
        omega

end Fabius
