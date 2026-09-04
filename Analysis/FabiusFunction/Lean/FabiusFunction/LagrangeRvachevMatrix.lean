import FabiusFunction.LagrangeRvachevSynthesis
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Matrix.Mul

/-!
# Finite matrix form of Lagrange--Rvachev synthesis

`FabiusFunction.LagrangeRvachevSynthesis` proves the scalar identities behind
the finite Lagrange--Rvachev decoder.  This module packages exactly those
identities as rectangular matrices.  For nodes indexed by a finite set `s`
and a nonzero mesh denominator `M`, the two matrices are

* the normalized encoder
  `A i k = M⁻¹ * rvachevUp F (v i - k / M)`, and
* the decoder
  `D k j = lagrangeRvachevDecoder s v M k j`.

The scalar cardinal-synthesis theorem gives `A * D = 1`.  The encoder has
nonnegative entries and row sum one, while every decoder row sums to one.
Thus `A` is a finite rectangular Markov kernel with an exact, generally
signed, right inverse.

The last two theorems isolate the sign obstruction without importing convex
geometry.  For any nonnegative matrix `A` and row-unital right inverse `D`, a
column that is strictly positive in two distinct rows of `A` forces a negative
entry in `D`.  The proof uses only the zero off-diagonal entries of `A * D`:
if `D` were nonnegative, every decoder row used by one encoder row would have
to be the corresponding coordinate vector.

This is deliberately only the finite Matrix/Markov layer.  It does not assert
the range, kernel, rank, trace, characteristic-polynomial, or Cauchy--Binet
claims of the larger projector package in the representation frontier.

## Main declarations

* `rvachevAtomIndexSet`, `RvachevAtomIndex` -- the exact finite lattice block
  used for synthesis on `[-1, 1]`.
* `lagrangeRvachevEncoderMatrix`, `lagrangeRvachevDecoderMatrix` -- the
  normalized encoder and unnormalized decoder.
* `lagrangeRvachevEncoderMatrix_nonneg` and
  `sum_lagrangeRvachevEncoderMatrix_row_eq_one` -- the rectangular Markov
  properties of the encoder.
* `sum_lagrangeRvachevDecoderMatrix_row_eq_one` -- decoder row unitality.
* `lagrangeRvachevEncoderMatrix_mul_decoderMatrix` -- the exact right-inverse
  identity.
* `exists_neg_entry_of_rightInverse_of_row_overlap` -- the generic finite
  sign obstruction.
* `exists_lagrangeRvachevDecoderMatrix_entry_neg_of_row_overlap` -- its
  Lagrange--Rvachev specialization.
-/

set_option autoImplicit false

open Polynomial Set
open scoped BigOperators

namespace Fabius

noncomputable section

/-- The finite integer block indexing every Rvachev translate that can
contribute to uniform synthesis on `[-1, 1]` at mesh denominator `M`.

The endpoints `±2M` are excluded because the corresponding translates
vanish at the boundary of the support. -/
def rvachevAtomIndexSet (M : ℕ) : Finset ℤ :=
  Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ))

/-- The finite type of Rvachev atom indices at mesh denominator `M`.  Using
the subtype of `rvachevAtomIndexSet M` makes the finite synthesis identities
available to the typed `Matrix` API without choosing an arbitrary enumeration
of the integer lattice block. -/
abbrev RvachevAtomIndex (M : ℕ) := ↥(rvachevAtomIndexSet M)

/-- The normalized finite Rvachev collocation matrix.  Its rows are the
interpolation nodes in `s`, its columns are the atom indices in
`rvachevAtomIndexSet M`, and the factor `M⁻¹` is the lattice spacing.

The definition is total at `M = 0`; the right-inverse and row-sum theorems
state the mathematically necessary hypothesis `M ≠ 0`. -/
def lagrangeRvachevEncoderMatrix
    (F : BoundedFabius) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℝ) (M : ℕ) :
    Matrix (↥s) (RvachevAtomIndex M) ℝ :=
  fun i k ↦
    ((M : ℝ))⁻¹ *
      rvachevUp F (v i.1 - (k.1 : ℝ) / (M : ℝ))

/-- The finite Lagrange--Rvachev decoder matrix.  Rows are atom indices and
columns are interpolation nodes.  Its entries are the sampled Rvachev
deconvolutions of the corresponding Lagrange basis polynomials.

The mesh normalization is carried by `lagrangeRvachevEncoderMatrix`, so this
matrix uses the unnormalized scalar decoder from
`LagrangeRvachevSynthesis`. -/
def lagrangeRvachevDecoderMatrix
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℝ) (M : ℕ) :
    Matrix (RvachevAtomIndex M) (↥s) ℝ :=
  fun k i ↦ lagrangeRvachevDecoder s v M k.1 i.1

private theorem sum_finsetSubtype_eq_sum
    {α A : Type*} [AddCommMonoid A]
    (s : Finset α) (f : α → A) :
    (∑ i : ↥s, f i.1) = ∑ i ∈ s, f i := by
  rw [Finset.univ_eq_attach, Finset.sum_attach]

/-- Every entry of the normalized Rvachev encoder is nonnegative.  This uses
only nonnegativity of `rvachevUp`; neither the Fabius equation, distinctness of
the interpolation nodes, nor a nonzero mesh is needed. -/
theorem lagrangeRvachevEncoderMatrix_nonneg
    (F : BoundedFabius) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℝ) (M : ℕ)
    (i : ↥s) (k : RvachevAtomIndex M) :
    0 ≤ lagrangeRvachevEncoderMatrix F s v M i k := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg M))
    (rvachevUp_nonneg F _)

/-- Every row of the normalized Rvachev encoder sums to one.  The node only
needs to lie in `[-1, 1]`, which is exactly the interval on which the global
partition sum truncates to `rvachevAtomIndexSet M`.

This is the row-normalization half of the rectangular Markov property.  It is
proved directly from constant polynomial synthesis, so it does not require
distinct interpolation nodes or the decoder degree bound. -/
theorem sum_lagrangeRvachevEncoderMatrix_row_eq_one
    (F : BoundedFabius) (hF : IsFabius F)
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℝ) {M : ℕ} (hM : M ≠ 0)
    (i : ↥s) (hvi : v i.1 ∈ Icc (-1 : ℝ) 1) :
    (∑ k : RvachevAtomIndex M,
      lagrangeRvachevEncoderMatrix F s v M i k) = 1 := by
  have hone : rvachevDeconvolvedPolynomial (1 : ℝ[X]) = 1 := by
    calc
      rvachevDeconvolvedPolynomial (1 : ℝ[X]) =
          rvachevAppellPolynomial 0 := by
        simpa only [pow_zero] using rvachevDeconvolvedPolynomial_X_pow 0
      _ = 1 := by simp [rvachevAppellPolynomial_eq_poly_cast]
  have hsynth :=
    normalized_sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp
      F hF hM (P := (1 : ℝ[X])) (by simp) hvi
  rw [hone] at hsynth
  simp only [Polynomial.eval_one, one_mul] at hsynth
  change
    (∑ k : RvachevAtomIndex M,
      ((M : ℝ))⁻¹ *
        rvachevUp F (v i.1 - (k.1 : ℝ) / (M : ℝ))) = 1
  calc
    (∑ k : RvachevAtomIndex M,
        ((M : ℝ))⁻¹ *
          rvachevUp F (v i.1 - (k.1 : ℝ) / (M : ℝ))) =
        ∑ k ∈ rvachevAtomIndexSet M,
          ((M : ℝ))⁻¹ *
            rvachevUp F (v i.1 - (k : ℝ) / (M : ℝ)) :=
      sum_finsetSubtype_eq_sum (rvachevAtomIndexSet M)
        (fun k : ℤ ↦
          ((M : ℝ))⁻¹ *
            rvachevUp F (v i.1 - (k : ℝ) / (M : ℝ)))
    _ = ((M : ℝ))⁻¹ *
          ∑ k ∈ rvachevAtomIndexSet M,
            (1 : ℝ) * rvachevUp F
              (v i.1 - (k : ℝ) / (M : ℝ)) := by
      rw [Finset.mul_sum]
      simp
    _ = 1 := by
      simpa only [one_mul, rvachevAtomIndexSet] using hsynth

/-- Every row of the Lagrange--Rvachev decoder sums to one for a nonempty
family of distinct interpolation nodes.  Equivalently, the decoder sends the
constant nodal data vector to the constant coefficient row.

No Fabius or mesh-admissibility hypothesis is needed: this is the finite
Lagrange partition of unity followed by polynomial deconvolution, which fixes
the constant polynomial. -/
theorem sum_lagrangeRvachevDecoderMatrix_row_eq_one
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℝ)
    (hvs : Set.InjOn v s) (hs : s.Nonempty)
    (M : ℕ) (k : RvachevAtomIndex M) :
    (∑ i : ↥s, lagrangeRvachevDecoderMatrix s v M k i) = 1 := by
  change (∑ i : ↥s, lagrangeRvachevDecoder s v M k.1 i.1) = 1
  calc
    (∑ i : ↥s, lagrangeRvachevDecoder s v M k.1 i.1) =
        ∑ i ∈ s, lagrangeRvachevDecoder s v M k.1 i :=
      sum_finsetSubtype_eq_sum s _
    _ = 1 := sum_lagrangeRvachevDecoder_eq_one s v hvs hs M k.1

/-- **Exact finite right inverse.**  The normalized Rvachev collocation
matrix times the Lagrange--Rvachev decoder is the identity on the indexed
interpolation nodes.

The hypotheses are exactly those of scalar componentwise biorthogonality:
the nodes are distinct and lie in `[-1, 1]`, the mesh is nonzero, and its
two-adic valuation supports every Lagrange basis degree `s.card - 1`.  This
theorem is a typed Matrix packaging of that scalar result; it makes no claim
about the larger coefficient-space projector `D * A`. -/
theorem lagrangeRvachevEncoderMatrix_mul_decoderMatrix
    (F : BoundedFabius) (hF : IsFabius F)
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℝ)
    (hvs : Set.InjOn v s)
    {M : ℕ} (hM : M ≠ 0)
    (hcard : s.card - 1 ≤ padicValNat 2 M)
    (hv : ∀ i ∈ s, v i ∈ Icc (-1 : ℝ) 1) :
    lagrangeRvachevEncoderMatrix F s v M *
        lagrangeRvachevDecoderMatrix s v M = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  change
    (∑ k : RvachevAtomIndex M,
      (((M : ℝ))⁻¹ *
          rvachevUp F (v i.1 - (k.1 : ℝ) / (M : ℝ))) *
        lagrangeRvachevDecoder s v M k.1 j.1) =
      if i = j then 1 else 0
  have hcomponent :=
    normalized_sum_Ioo_lagrangeRvachevDecoder_eval_node
      F hF s v hvs (i := j.1) (j := i.1)
        j.2 i.2 hM hcard (hv i.1 i.2)
  calc
    (∑ k : RvachevAtomIndex M,
        (((M : ℝ))⁻¹ *
            rvachevUp F (v i.1 - (k.1 : ℝ) / (M : ℝ))) *
          lagrangeRvachevDecoder s v M k.1 j.1) =
        ∑ k ∈ rvachevAtomIndexSet M,
          (((M : ℝ))⁻¹ *
              rvachevUp F (v i.1 - (k : ℝ) / (M : ℝ))) *
            lagrangeRvachevDecoder s v M k j.1 :=
      sum_finsetSubtype_eq_sum (rvachevAtomIndexSet M)
        (fun k : ℤ ↦
          (((M : ℝ))⁻¹ *
              rvachevUp F (v i.1 - (k : ℝ) / (M : ℝ))) *
            lagrangeRvachevDecoder s v M k j.1)
    _ = ((M : ℝ))⁻¹ *
          ∑ k ∈ rvachevAtomIndexSet M,
            lagrangeRvachevDecoder s v M k j.1 *
              rvachevUp F (v i.1 - (k : ℝ) / (M : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = if i.1 = j.1 then 1 else 0 := by
      simpa only [rvachevAtomIndexSet] using hcomponent
    _ = if i = j then 1 else 0 := by
      simp only [Subtype.ext_iff]

/-- **Overlap forces a signed right inverse.**  Let `A` be a nonnegative
finite rectangular matrix and let `D` be a right inverse whose rows sum to
one.  If one column of `A` is strictly positive in two distinct rows, then
some entry of `D` is negative.

Encoder row normalization is not used: nonnegativity, `A * D = 1`, decoder
row unitality, and the stated overlap are the exact algebraic hypotheses.  If
`D` were nonnegative, the off-diagonal zero entries of `A * D` would force the
overlapping decoder row to be two different coordinate vectors. -/
theorem exists_neg_entry_of_rightInverse_of_row_overlap
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n ℝ) (D : Matrix n m ℝ)
    (hA : ∀ i k, 0 ≤ A i k)
    (hDrow : ∀ k, (∑ j, D k j) = 1)
    (hAD : A * D = 1)
    {i₁ i₂ : m} (hi : i₁ ≠ i₂) {k : n}
    (hik₁ : 0 < A i₁ k) (hik₂ : 0 < A i₂ k) :
    ∃ k' j, D k' j < 0 := by
  classical
  by_contra hneg
  have hDnonneg : ∀ k' j, 0 ≤ D k' j := by
    intro k' j
    exact le_of_not_gt fun hlt ↦ hneg ⟨k', j, hlt⟩
  have hvanish (i : m) (hik : 0 < A i k) (j : m) (hji : j ≠ i) :
      D k j = 0 := by
    have hentry := congrFun (congrFun hAD i) j
    rw [Matrix.mul_apply, Matrix.one_apply, if_neg (Ne.symm hji)] at hentry
    have hterms : (fun k' ↦ A i k' * D k' j) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg
        (fun k' ↦ mul_nonneg (hA i k') (hDnonneg k' j))).mp hentry
    have hterm : A i k * D k j = 0 := by
      simpa only [Pi.zero_apply] using congrFun hterms k
    exact (mul_eq_zero.mp hterm).resolve_left hik.ne'
  have hki₁ : D k i₁ = 1 := by
    calc
      D k i₁ = ∑ j : m, D k j := by
        symm
        apply Finset.sum_eq_single i₁
        · intro j _hj hji
          exact hvanish i₁ hik₁ j hji
        · simp
      _ = 1 := hDrow k
  have hki₁zero : D k i₁ = 0 :=
    hvanish i₂ hik₂ i₁ hi
  exact zero_ne_one (hki₁zero.symm.trans hki₁)

/-- A strictly overlapping pair of rows in the normalized Rvachev encoder
forces a negative entry in its exact Lagrange decoder.

Together with `lagrangeRvachevEncoderMatrix_nonneg`,
`sum_lagrangeRvachevEncoderMatrix_row_eq_one`,
`sum_lagrangeRvachevDecoderMatrix_row_eq_one`, and
`lagrangeRvachevEncoderMatrix_mul_decoderMatrix`, this is the complete finite
Markov-encoder/signed-decoder statement.  It remains conditional on an actual
strictly positive overlap, exactly as the source proposition does. -/
theorem exists_lagrangeRvachevDecoderMatrix_entry_neg_of_row_overlap
    (F : BoundedFabius) (hF : IsFabius F)
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℝ)
    (hvs : Set.InjOn v s)
    {M : ℕ} (hM : M ≠ 0)
    (hcard : s.card - 1 ≤ padicValNat 2 M)
    (hv : ∀ i ∈ s, v i ∈ Icc (-1 : ℝ) 1)
    {i₁ i₂ : ↥s} (hi : i₁ ≠ i₂) {k : RvachevAtomIndex M}
    (hik₁ : 0 < lagrangeRvachevEncoderMatrix F s v M i₁ k)
    (hik₂ : 0 < lagrangeRvachevEncoderMatrix F s v M i₂ k) :
    ∃ k' j, lagrangeRvachevDecoderMatrix s v M k' j < 0 := by
  have hs : s.Nonempty := ⟨i₁.1, i₁.2⟩
  exact exists_neg_entry_of_rightInverse_of_row_overlap
    (lagrangeRvachevEncoderMatrix F s v M)
    (lagrangeRvachevDecoderMatrix s v M)
    (lagrangeRvachevEncoderMatrix_nonneg F s v M)
    (sum_lagrangeRvachevDecoderMatrix_row_eq_one s v hvs hs M)
    (lagrangeRvachevEncoderMatrix_mul_decoderMatrix
      F hF s v hvs hM hcard hv)
    hi hik₁ hik₂

end

end Fabius
