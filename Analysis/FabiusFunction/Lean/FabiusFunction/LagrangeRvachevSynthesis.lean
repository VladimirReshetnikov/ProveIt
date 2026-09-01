import FabiusFunction.GeometricLagrange
import FabiusFunction.RvachevPolynomialSynthesis

/-!
# Lagrange interpolation through finite Rvachev dictionaries

This module combines Mathlib's finite Lagrange basis with the exact
polynomial-synthesis theorem for shifted Rvachev atoms.  For a finite family
of real nodes, the Rvachev deconvolution of each Lagrange basis polynomial
gives one column of a finite decoder.  The resulting atom expansion
reconstructs every basis polynomial, hence every Lagrange interpolant, on
`[-1, 1]` whenever the mesh has enough two-adic valuation for the number of
nodes.

The construction is deliberately independent of geometric nodes.  A later
specialization may take `s = range (n + 1)`, `v j = c * q ^ j`, and
`M = 2 ^ n`; the results here already supply the cardinal decoder,
componentwise biorthogonality, linear data-to-atom transform, and exact
finite interpolation loop needed by that specialization.

## Main definitions and results

* `lagrangeRvachevDecoder` is the sampled deconvolution of one Lagrange basis
  polynomial.
* `lagrangeRvachevAtomCoefficient` applies the finite decoder to nodal data
  and includes the lattice normalization `1 / M`.
* `normalized_sum_Ioo_lagrangeRvachevDecoder_mul_shifted_rvachevUp`
  reconstructs one Lagrange cardinal on `[-1, 1]`.
* `normalized_sum_Ioo_lagrangeRvachevDecoder_eval_node` is the corresponding
  Kronecker-delta identity at the interpolation nodes.
* `sum_Ioo_lagrangeRvachevAtomCoefficient_mul_shifted_rvachevUp`
  reconstructs the full Lagrange interpolant from its finite atom dictionary.
* `sum_lagrangeRvachevDecoder_eq_one` shows that every decoder row has total
  mass one for a nonempty family of distinct nodes.
-/

set_option autoImplicit false

open Polynomial Set
open scoped BigOperators

namespace Fabius

noncomputable section

/-- The Rvachev decoder entry attached to the Lagrange basis polynomial at
index `i`, sampled at the lattice point `k / M`.

The definition is total in `M`; reconstruction theorems separately assume
`M ≠ 0`. -/
def lagrangeRvachevDecoder
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ)
    (M : ℕ) (k : ℤ) (i : ι) : ℝ :=
  (rvachevDeconvolvedPolynomial (Lagrange.basis s v i)).eval
    ((k : ℝ) / (M : ℝ))

/-- The normalized coefficient of the shifted Rvachev atom indexed by `k`
for Lagrange data `y`.  It is the decoder row applied to the finite data
vector, multiplied by the lattice spacing `1 / M`. -/
def lagrangeRvachevAtomCoefficient
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v y : ι → ℝ)
    (M : ℕ) (k : ℤ) : ℝ :=
  ((M : ℝ))⁻¹ *
    ∑ i ∈ s, lagrangeRvachevDecoder s v M k i * y i

/-- A Lagrange basis polynomial indexed by a member of `s` has natural
degree at most `s.card - 1`, even when node collisions make one of its
normalized linear factors vanish. -/
theorem natDegree_lagrangeBasis_le_card_sub_one
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ)
    {i : ι} (hi : i ∈ s) :
    (Lagrange.basis s v i).natDegree ≤ s.card - 1 := by
  classical
  rw [Lagrange.basis]
  calc
    (∏ j ∈ s.erase i, Lagrange.basisDivisor (v i) (v j)).natDegree ≤
        ∑ j ∈ s.erase i,
          (Lagrange.basisDivisor (v i) (v j)).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ s.erase i, 1 := by
      apply Finset.sum_le_sum
      intro j _hj
      by_cases hij : v i = v j
      · simp [hij, Lagrange.natDegree_basisDivisor_self]
      · rw [Lagrange.natDegree_basisDivisor_of_ne hij]
    _ = (s.erase i).card := by simp
    _ = s.card - 1 := Finset.card_erase_of_mem hi

/-- Every finite Lagrange interpolant has natural degree at most one less
than the number of indexed nodes.  This upper bound does not require
distinct nodes; collisions can only lower the degrees of basis factors. -/
theorem natDegree_lagrangeInterpolate_le_card_sub_one
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v y : ι → ℝ) :
    (Lagrange.interpolate s v y).natDegree ≤ s.card - 1 := by
  classical
  rw [Lagrange.interpolate_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_C_mul_le (y i) (Lagrange.basis s v i)).trans
    (natDegree_lagrangeBasis_le_card_sub_one s v hi)

/-- **Finite Rvachev synthesis of a Lagrange cardinal.**  If the mesh's
two-adic valuation is at least `s.card - 1`, the normalized finite dictionary
of decoder samples reconstructs the Lagrange basis polynomial on `[-1, 1]`.

Distinctness of the nodes is not needed for this synthesis statement; it is
needed only when the basis is interpreted as a cardinal function. -/
theorem normalized_sum_Ioo_lagrangeRvachevDecoder_mul_shifted_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ)
    {i : ι} (hi : i ∈ s)
    {M : ℕ} (hM : M ≠ 0)
    (hcard : s.card - 1 ≤ padicValNat 2 M)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ((M : ℝ))⁻¹ *
        ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
          lagrangeRvachevDecoder s v M k i *
            rvachevUp F (x - (k : ℝ) / (M : ℝ)) =
      (Lagrange.basis s v i).eval x := by
  simpa only [lagrangeRvachevDecoder] using
    normalized_sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp
      F hF hM
        ((natDegree_lagrangeBasis_le_card_sub_one s v hi).trans hcard) hx

/-- **Componentwise Lagrange--Rvachev biorthogonality.**  Evaluating the
finite cardinal synthesis at another indexed node gives the Kronecker delta.
The interval hypothesis is exactly what permits the uniform finite truncation
of the global Rvachev synthesis. -/
theorem normalized_sum_Ioo_lagrangeRvachevDecoder_eval_node
    (F : BoundedFabius) (hF : IsFabius F)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ)
    (hvs : Set.InjOn v s)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    {M : ℕ} (hM : M ≠ 0)
    (hcard : s.card - 1 ≤ padicValNat 2 M)
    (hvj : v j ∈ Icc (-1 : ℝ) 1) :
    ((M : ℝ))⁻¹ *
        ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
          lagrangeRvachevDecoder s v M k i *
            rvachevUp F (v j - (k : ℝ) / (M : ℝ)) =
      if j = i then 1 else 0 := by
  rw [normalized_sum_Ioo_lagrangeRvachevDecoder_mul_shifted_rvachevUp
    F hF s v hi hM hcard hvj]
  by_cases hji : j = i
  · subst j
    simp [hvs, hi]
  · rw [if_neg hji, Lagrange.eval_basis_of_ne (Ne.symm hji) hj]

/-- Applying the Rvachev decoder row to data is the same as sampling the
deconvolution of the corresponding Lagrange interpolant.  This is the finite
linearity identity behind the atom-coefficient transform. -/
theorem lagrangeRvachevAtomCoefficient_eq_deconvolved_interpolate
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v y : ι → ℝ)
    (M : ℕ) (k : ℤ) :
    lagrangeRvachevAtomCoefficient s v y M k =
      ((M : ℝ))⁻¹ *
        (rvachevDeconvolvedPolynomial (Lagrange.interpolate s v y)).eval
          ((k : ℝ) / (M : ℝ)) := by
  classical
  rw [lagrangeRvachevAtomCoefficient, Lagrange.interpolate_apply,
    rvachevDeconvolvedPolynomial_finsetSum, Polynomial.eval_finsetSum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  rw [rvachevDeconvolvedPolynomial_C_mul, Polynomial.eval_mul,
    Polynomial.eval_C, lagrangeRvachevDecoder]
  ring

/-- **Interpolation through a finite Rvachev dictionary.**  The normalized
decoder coefficients reconstruct the entire Lagrange interpolant on
`[-1, 1]`.  No node-injectivity hypothesis is required for this polynomial
identity; distinctness matters only when the polynomial is used to recover
the supplied data at the nodes. -/
theorem sum_Ioo_lagrangeRvachevAtomCoefficient_mul_shifted_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v y : ι → ℝ)
    {M : ℕ} (hM : M ≠ 0)
    (hcard : s.card - 1 ≤ padicValNat 2 M)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
        lagrangeRvachevAtomCoefficient s v y M k *
          rvachevUp F (x - (k : ℝ) / (M : ℝ)) =
      (Lagrange.interpolate s v y).eval x := by
  calc
    (∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
        lagrangeRvachevAtomCoefficient s v y M k *
          rvachevUp F (x - (k : ℝ) / (M : ℝ))) =
        ((M : ℝ))⁻¹ *
          ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
            (rvachevDeconvolvedPolynomial
                (Lagrange.interpolate s v y)).eval
                ((k : ℝ) / (M : ℝ)) *
              rvachevUp F (x - (k : ℝ) / (M : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [lagrangeRvachevAtomCoefficient_eq_deconvolved_interpolate]
      ring
    _ = (Lagrange.interpolate s v y).eval x :=
      normalized_sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp
        F hF hM
          ((natDegree_lagrangeInterpolate_le_card_sub_one s v y).trans hcard)
          hx

/-- Every decoder row sums to one for a nonempty family of distinct nodes.
This is the coefficient-side counterpart of the partition of unity for the
Lagrange basis; Rvachev deconvolution preserves the constant polynomial. -/
theorem sum_lagrangeRvachevDecoder_eq_one
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ)
    (hvs : Set.InjOn v s) (hs : s.Nonempty)
    (M : ℕ) (k : ℤ) :
    ∑ i ∈ s, lagrangeRvachevDecoder s v M k i = 1 := by
  classical
  have hone : rvachevDeconvolvedPolynomial (1 : ℝ[X]) = 1 := by
    calc
      rvachevDeconvolvedPolynomial (1 : ℝ[X]) =
          rvachevAppellPolynomial 0 := by
        simpa only [pow_zero] using
          (rvachevDeconvolvedPolynomial_X_pow 0)
      _ = 1 := by simp [rvachevAppellPolynomial_eq_poly_cast]
  simp_rw [lagrangeRvachevDecoder]
  rw [← Polynomial.eval_finsetSum,
    ← rvachevDeconvolvedPolynomial_finsetSum,
    Lagrange.sum_basis hvs hs, hone, Polynomial.eval_one]

end

end Fabius
