import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Inversion of smoothing operators on polynomials

The inverse volume's roadmap carries a *Polynomial smoothing and
inverse moment operator* obligation: for a polynomial `q` of degree at
most `r`, the smoothing identity `M(aD)q = J` should invert to the
finite formula `q = ∑_{j ≤ ⌊r/2⌋} (-1)^j b_j a^{2j} D^{2j} J`, where
`1/M(t) = ∑ (-1)^j b_j t^{2j}` — "only finite sums after the degree
bound is known; no convergence theorem for formal differential
operators is needed".

This module proves that in full generality, as the operator calculus
of formal power series acting on polynomials through `aD` over any
commutative semiring:

* `seriesDerivOp φ a q` — the action `φ(aD)q := ∑_m φ_m a^m q^{(m)}`,
  a finite sum because derivatives beyond the degree vanish; no
  topology on the coefficient ring is involved.
* `seriesDerivOp_mul` — **substitution is multiplicative**:
  `(φψ)(aD) q = φ(aD)(ψ(aD)q)`.  The Cauchy product of the series
  matches the composition of the operators; the double sum collapses
  along antidiagonals because all terms beyond the degree vanish.
* `seriesDerivOp_left_inverse` — for mutually inverse series
  (`φ·ψ = 1`) the operators cancel on every polynomial: `ψ(aD)` is a
  two-sided inverse of `φ(aD)` on polynomials.
* `eq_seriesDerivOp_of_seriesDerivOp_eq` — the obligation's
  implication: `φ(aD)q = J` forces `q = ψ(aD)J`.
* `seriesDerivOp_eq_sum_even`, `eq_sum_even_of_seriesDerivOp_eq` — for
  an even reciprocal series (all odd coefficients zero, as for the
  reciprocal moment generating function of a symmetric law) the
  inverse truncates at `⌊r/2⌋`, giving the displayed formula
  `q = ∑_{j=0}^{⌊r/2⌋} ψ_{2j} a^{2j} D^{2j} J` verbatim.

The Fabius instance takes `φ` to be the moment series of the dyadic
random series `Y` and `ψ` its reciprocal `∑ (-1)^j b_j t^{2j}` — the
reciprocal-sinc coefficients; the theorems here are the complete
formal half of the exact local polynomial theorem, with no analytic
input.
-/

set_option autoImplicit false

open Polynomial PowerSeries Finset

namespace Fabius

variable {R : Type*} [CommSemiring R]

/-- A formal power series `φ` acts on a polynomial `q` as the
differential operator `φ(aD)`: the finite sum
`∑_{m ≤ deg q} φ_m a^m q^{(m)}`.  No convergence is involved — the
degree bound truncates the series exactly. -/
noncomputable def seriesDerivOp (φ : PowerSeries R) (a : R) (q : R[X]) : R[X] :=
  ∑ m ∈ Finset.range (q.natDegree + 1),
    (PowerSeries.coeff m φ * a ^ m) • derivative^[m] q

/-- The action never raises the degree. -/
theorem natDegree_seriesDerivOp_le (φ : PowerSeries R) (a : R) (q : R[X]) :
    (seriesDerivOp φ a q).natDegree ≤ q.natDegree :=
  natDegree_sum_le_of_forall_le _ _ fun m _ =>
    (natDegree_smul_le _ _).trans
      ((natDegree_iterate_derivative q m).trans (Nat.sub_le _ _))

/-- The defining sum is stable under enlarging the range: any bound
beyond the degree computes the same operator value. -/
theorem seriesDerivOp_eq_sum_range {q : R[X]} {N : ℕ} (hN : q.natDegree < N)
    (φ : PowerSeries R) (a : R) :
    seriesDerivOp φ a q =
      ∑ m ∈ Finset.range N,
        (PowerSeries.coeff m φ * a ^ m) • derivative^[m] q := by
  simp only [seriesDerivOp]
  refine Finset.sum_subset
    (Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega))
    fun m _ hm => ?_
  have hdeg : q.natDegree < m := by
    by_contra h
    exact hm (Finset.mem_range.mpr (by omega))
  rw [Polynomial.iterate_derivative_eq_zero hdeg, smul_zero]

/-- The constant series `1` acts as the identity. -/
@[simp] theorem seriesDerivOp_one (a : R) (q : R[X]) :
    seriesDerivOp 1 a q = q := by
  simp only [seriesDerivOp]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro m _ hm
    rw [PowerSeries.coeff_one, if_neg hm, zero_mul, zero_smul]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

/-- **Substitution `t ↦ aD` is multiplicative**: the product of two
power series acts as the composition of their operators.  The Cauchy
product regroups the composed double sum along antidiagonals; the
terms the antidiagonal band misses all differentiate the polynomial
past its degree and vanish. -/
theorem seriesDerivOp_mul (φ ψ : PowerSeries R) (a : R) (q : R[X]) :
    seriesDerivOp (φ * ψ) a q = seriesDerivOp φ a (seriesDerivOp ψ a q) := by
  classical
  have hdisj : (↑(Finset.range (q.natDegree + 1)) : Set ℕ).PairwiseDisjoint
      Finset.antidiagonal := by
    intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hpi hpj
    rw [Finset.mem_antidiagonal] at hpi hpj
    exact hij (hpi.symm.trans hpj)
  have hsub : (Finset.range (q.natDegree + 1)).biUnion Finset.antidiagonal ⊆
      Finset.range (q.natDegree + 1) ×ˢ Finset.range (q.natDegree + 1) := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨n, hn, hpn⟩ := hp
    rw [Finset.mem_antidiagonal] at hpn
    rw [Finset.mem_range] at hn
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    omega
  have hvan : ∀ p ∈ Finset.range (q.natDegree + 1) ×ˢ
      Finset.range (q.natDegree + 1),
      p ∉ (Finset.range (q.natDegree + 1)).biUnion Finset.antidiagonal →
      ((PowerSeries.coeff p.1 φ * PowerSeries.coeff p.2 ψ) *
          a ^ (p.1 + p.2)) • derivative^[p.1 + p.2] q = 0 := by
    intro p _ hpB
    have hge : q.natDegree + 1 ≤ p.1 + p.2 := by
      by_contra hlt
      exact hpB (Finset.mem_biUnion.mpr
        ⟨p.1 + p.2, Finset.mem_range.mpr (by omega),
          Finset.mem_antidiagonal.mpr rfl⟩)
    rw [Polynomial.iterate_derivative_eq_zero (by omega), smul_zero]
  have hpush : ∀ m : ℕ,
      (PowerSeries.coeff m φ * a ^ m) • derivative^[m] (seriesDerivOp ψ a q) =
        ∑ k ∈ Finset.range (q.natDegree + 1),
          ((PowerSeries.coeff m φ * PowerSeries.coeff k ψ) * a ^ (m + k)) •
            derivative^[m + k] q := by
    intro m
    simp only [seriesDerivOp]
    rw [Polynomial.iterate_derivative_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.iterate_derivative_smul, smul_smul,
      ← Function.iterate_add_apply, mul_mul_mul_comm, ← pow_add]
  calc seriesDerivOp (φ * ψ) a q
      = ∑ n ∈ Finset.range (q.natDegree + 1),
          (PowerSeries.coeff n (φ * ψ) * a ^ n) • derivative^[n] q := rfl
    _ = ∑ n ∈ Finset.range (q.natDegree + 1), ∑ p ∈ Finset.antidiagonal n,
          ((PowerSeries.coeff p.1 φ * PowerSeries.coeff p.2 ψ) *
            a ^ (p.1 + p.2)) • derivative^[p.1 + p.2] q := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [PowerSeries.coeff_mul, Finset.sum_mul, Finset.sum_smul]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.mem_antidiagonal] at hp
        rw [← hp]
    _ = ∑ p ∈ (Finset.range (q.natDegree + 1)).biUnion Finset.antidiagonal,
          ((PowerSeries.coeff p.1 φ * PowerSeries.coeff p.2 ψ) *
            a ^ (p.1 + p.2)) • derivative^[p.1 + p.2] q :=
        (Finset.sum_biUnion hdisj).symm
    _ = ∑ p ∈ Finset.range (q.natDegree + 1) ×ˢ
          Finset.range (q.natDegree + 1),
          ((PowerSeries.coeff p.1 φ * PowerSeries.coeff p.2 ψ) *
            a ^ (p.1 + p.2)) • derivative^[p.1 + p.2] q :=
        Finset.sum_subset hsub hvan
    _ = ∑ m ∈ Finset.range (q.natDegree + 1),
          ∑ k ∈ Finset.range (q.natDegree + 1),
          ((PowerSeries.coeff m φ * PowerSeries.coeff k ψ) * a ^ (m + k)) •
            derivative^[m + k] q := Finset.sum_product ..
    _ = seriesDerivOp φ a (seriesDerivOp ψ a q) := by
        rw [seriesDerivOp_eq_sum_range
          (lt_of_le_of_lt (natDegree_seriesDerivOp_le ψ a q)
            (Nat.lt_succ_self _)) φ a]
        exact Finset.sum_congr rfl fun m _ => (hpush m).symm

/-- For mutually inverse power series, the operators cancel on every
polynomial: `ψ(aD)(φ(aD)q) = q`. -/
theorem seriesDerivOp_left_inverse {φ ψ : PowerSeries R} (h : φ * ψ = 1)
    (a : R) (q : R[X]) :
    seriesDerivOp ψ a (seriesDerivOp φ a q) = q := by
  rw [← seriesDerivOp_mul, mul_comm, h, seriesDerivOp_one]

/-- **The smoothing inversion**: if `φ(aD)q = J` and `ψ` is the
reciprocal series of `φ`, then `q = ψ(aD)J`. -/
theorem eq_seriesDerivOp_of_seriesDerivOp_eq {φ ψ : PowerSeries R}
    (h : φ * ψ = 1) {a : R} {q J : R[X]}
    (hqJ : seriesDerivOp φ a q = J) :
    q = seriesDerivOp ψ a J := by
  rw [← hqJ, seriesDerivOp_left_inverse h]

/- A private unpaired variant of `Fabius.sum_range_two_mul`
(`DyadicClosedForm.lean`): duplicated here because this module sits
below that file in the import DAG and depends only on Mathlib. -/
private theorem sum_range_two_mul (K : ℕ) (g : ℕ → R[X]) :
    ∑ m ∈ Finset.range (2 * K), g m =
      ∑ j ∈ Finset.range K, g (2 * j) +
        ∑ j ∈ Finset.range K, g (2 * j + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, Finset.sum_range_succ,
        Finset.sum_range_succ]
      abel

/-- For an **even** series (all odd coefficients vanish, as for the
reciprocal moment series of a symmetric law), the action on a
polynomial of degree at most `r` truncates at `⌊r/2⌋`:
`ψ(aD)J = ∑_{j=0}^{⌊r/2⌋} ψ_{2j} a^{2j} D^{2j} J`. -/
theorem seriesDerivOp_eq_sum_even {ψ : PowerSeries R}
    (hodd : ∀ k, Odd k → PowerSeries.coeff k ψ = 0) (a : R) {J : R[X]}
    {r : ℕ} (hJ : J.natDegree ≤ r) :
    seriesDerivOp ψ a J =
      ∑ j ∈ Finset.range (r / 2 + 1),
        (PowerSeries.coeff (2 * j) ψ * a ^ (2 * j)) •
          derivative^[2 * j] J := by
  rw [seriesDerivOp_eq_sum_range
      (show J.natDegree < 2 * (r / 2 + 1) by omega) ψ a,
    sum_range_two_mul]
  have hzero : ∑ j ∈ Finset.range (r / 2 + 1),
      (PowerSeries.coeff (2 * j + 1) ψ * a ^ (2 * j + 1)) •
        derivative^[2 * j + 1] J = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [hodd (2 * j + 1) ⟨j, by ring⟩, zero_mul, zero_smul]
  rw [hzero, add_zero]

/-- **The obligation's displayed form**: for a polynomial `q` of
degree at most `r`, from `φ(aD)q = J` and an even reciprocal series
`ψ = φ⁻¹` one reads off
`q = ∑_{j=0}^{⌊r/2⌋} ψ_{2j} a^{2j} D^{2j} J` — with
`ψ_{2j} = (-1)^j b_j` this is exactly
`q = ∑_{j=0}^{⌊r/2⌋} (-1)^j b_j a^{2j} D^{2j} J`, by finite sums
alone. -/
theorem eq_sum_even_of_seriesDerivOp_eq {φ ψ : PowerSeries R}
    (h : φ * ψ = 1) (hodd : ∀ k, Odd k → PowerSeries.coeff k ψ = 0)
    {a : R} {q J : R[X]} {r : ℕ} (hq : q.natDegree ≤ r)
    (hqJ : seriesDerivOp φ a q = J) :
    q = ∑ j ∈ Finset.range (r / 2 + 1),
        (PowerSeries.coeff (2 * j) ψ * a ^ (2 * j)) •
          derivative^[2 * j] J := by
  have hJr : J.natDegree ≤ r := by
    rw [← hqJ]
    exact (natDegree_seriesDerivOp_le φ a q).trans hq
  calc q = seriesDerivOp ψ a J := eq_seriesDerivOp_of_seriesDerivOp_eq h hqJ
    _ = _ := seriesDerivOp_eq_sum_even hodd a hJr

end Fabius
