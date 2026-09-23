import Surreal.Algebra.PolynomialResiduePairing
import Surreal.Algebra.PolynomialResidueGram
import Mathlib.RingTheory.Trace.Basic

/-!
# The quadratic algebra and its collision-stable residue pairing

Specializing the monic quotient to `X²-d` proves the algebra, basis,
pairing matrix, multiplication matrix and trace clauses of
`trigonometry:eq:quadalgebra` and `trigonometry:thm:residuepairing`.
The coefficient ring is arbitrary and nontrivial, including rings with
zero divisors and positive characteristic; no root separation is inverted.
-/

namespace Surreal.FinitePolynomial

open Polynomial Module

noncomputable section

variable {R : Type*} [CommRing R]

/-- The monic polynomial defining the quadratic collision algebra. -/
def quadraticPolynomial (d : R) : R[X] := X ^ 2 - C d

theorem quadraticPolynomial_monic (d : R) : (quadraticPolynomial d).Monic :=
  monic_X_pow_sub_C d (by decide)

/-- The native polynomial quotient retains both dimensions at a collision. -/
abbrev quadraticQuotient (d : R) := AdjoinRoot (quadraticPolynomial d)

/-- The distinguished quadratic coordinate. -/
def quadraticRoot (d : R) : quadraticQuotient d := AdjoinRoot.root (quadraticPolynomial d)

@[simp] theorem quadraticRoot_sq (d : R) :
    quadraticRoot d ^ 2 = algebraMap R (quadraticQuotient d) d := by
  have h : AdjoinRoot.mk (quadraticPolynomial d) (quadraticPolynomial d) = 0 :=
    AdjoinRoot.mk_self
  change AdjoinRoot.mk (quadraticPolynomial d) (X ^ 2 - C d) = 0 at h
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  exact sub_eq_zero.mp h

variable [Nontrivial R]

@[simp] theorem quadraticPolynomial_natDegree (d : R) : (quadraticPolynomial d).natDegree = 2 :=
  natDegree_X_pow_sub_C

/-- The power basis, reindexed by exactly `Fin 2`. -/
def quadraticBasis (d : R) : Basis (Fin 2) R (quadraticQuotient d) :=
  (AdjoinRoot.powerBasis' (quadraticPolynomial_monic d)).basis.reindex
    (finCongr (quadraticPolynomial_natDegree d))

theorem quadraticBasis_apply (d : R) (i : Fin 2) :
    quadraticBasis d i = quadraticRoot d ^ (i : ℕ) := by
  rw [quadraticBasis, Basis.reindex_apply]
  exact (AdjoinRoot.powerBasis' (quadraticPolynomial_monic d)).basis_eq_pow _

@[simp] theorem quadraticBasis_zero (d : R) : quadraticBasis d 0 = 1 := by
  rw [quadraticBasis_apply]
  rfl

@[simp] theorem quadraticBasis_one (d : R) : quadraticBasis d 1 = quadraticRoot d := by
  rw [quadraticBasis_apply]
  exact pow_one _

/-- The dimension is two even when `d=0` or the coefficient ring has zero divisors. -/
theorem quadraticQuotient_finrank (d : R) : Module.finrank R (quadraticQuotient d) = 2 := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (quadraticBasis d)

theorem quadraticBasis_repr (d : R) (z : quadraticQuotient d) (i : Fin 2) :
    (quadraticBasis d).repr z i =
      (AdjoinRoot.modByMonicHom (quadraticPolynomial_monic d) z).coeff i := by
  rw [quadraticBasis, Basis.repr_reindex_apply]
  rfl

/-- The constant coordinate of the unique quadratic remainder. -/
def quadraticConstant (d : R) : quadraticQuotient d →ₗ[R] R :=
  (Polynomial.lcoeff R 0).comp (AdjoinRoot.modByMonicHom (quadraticPolynomial_monic d))

/-- The coefficient of `W`, namely the monic-quotient residue functional. -/
def quadraticResidue (d : R) : quadraticQuotient d →ₗ[R] R :=
  residueFunctional (quadraticPolynomial d) (quadraticPolynomial_monic d)

omit [Nontrivial R] in
@[simp] theorem quadraticConstant_mk (d : R) (g : R[X]) :
    quadraticConstant d (AdjoinRoot.mk (quadraticPolynomial d) g) =
      (g %ₘ quadraticPolynomial d).coeff 0 := rfl

@[simp] theorem quadraticResidue_mk (d : R) (g : R[X]) :
    quadraticResidue d (AdjoinRoot.mk (quadraticPolynomial d) g) =
      (g %ₘ quadraticPolynomial d).coeff 1 := by
  simp only [quadraticResidue, residueFunctional_mk, quadraticPolynomial_natDegree]

theorem quadraticConstant_eq_repr (d : R) (z : quadraticQuotient d) :
    quadraticConstant d z = (quadraticBasis d).repr z 0 := by
  rw [quadraticBasis_repr]
  rfl

theorem quadraticResidue_eq_repr (d : R) (z : quadraticQuotient d) :
    quadraticResidue d z = (quadraticBasis d).repr z 1 := by
  rw [quadraticBasis_repr]
  change (AdjoinRoot.modByMonicHom (quadraticPolynomial_monic d) z).coeff
    ((quadraticPolynomial d).natDegree - 1) = _
  rw [quadraticPolynomial_natDegree]
  rfl

/-- Every element is its unique linear remainder in `1,W`. -/
theorem quadratic_eq_scalar_add_mul_root (d : R) (z : quadraticQuotient d) :
    z = algebraMap R (quadraticQuotient d) (quadraticConstant d z) +
      algebraMap R (quadraticQuotient d) (quadraticResidue d z) * quadraticRoot d := by
  rw [quadraticConstant_eq_repr, quadraticResidue_eq_repr]
  have h := (quadraticBasis d).sum_repr z
  simpa only [Fin.sum_univ_two, quadraticBasis_zero, quadraticBasis_one,
    Algebra.smul_def, mul_one] using h.symm

private theorem quadratic_scalar_add_mul_root_eq_basis (d a b : R) :
    algebraMap R (quadraticQuotient d) a + algebraMap R (quadraticQuotient d) b * quadraticRoot d =
      a • quadraticBasis d 0 + b • quadraticBasis d 1 := by
  simp only [quadraticBasis_zero, quadraticBasis_one, Algebra.smul_def, mul_one]

@[simp] theorem quadraticConstant_scalar_add_mul_root (d a b : R) :
    quadraticConstant d (algebraMap R (quadraticQuotient d) a +
      algebraMap R (quadraticQuotient d) b * quadraticRoot d) = a := by
  rw [quadraticConstant_eq_repr, quadratic_scalar_add_mul_root_eq_basis]
  simp only [map_add, map_smul, Basis.repr_self]
  simp

@[simp] theorem quadraticResidue_scalar_add_mul_root (d a b : R) :
    quadraticResidue d (algebraMap R (quadraticQuotient d) a +
      algebraMap R (quadraticQuotient d) b * quadraticRoot d) = b := by
  rw [quadraticResidue_eq_repr, quadratic_scalar_add_mul_root_eq_basis]
  simp only [map_add, map_smul, Basis.repr_self]
  simp

/-- Equality is exactly equality of the two remainder coordinates. -/
theorem quadratic_ext {d : R} {z w : quadraticQuotient d}
    (ha : quadraticConstant d z = quadraticConstant d w)
    (hb : quadraticResidue d z = quadraticResidue d w) : z = w := by
  rw [quadratic_eq_scalar_add_mul_root d z, quadratic_eq_scalar_add_mul_root d w, ha, hb]

/-- A unique pair of coefficients represents each quotient element. -/
theorem existsUnique_quadratic_representation (d : R) (z : quadraticQuotient d) :
    ∃! ab : R × R, z = algebraMap R (quadraticQuotient d) ab.1 +
      algebraMap R (quadraticQuotient d) ab.2 * quadraticRoot d := by
  refine ⟨(quadraticConstant d z, quadraticResidue d z), quadratic_eq_scalar_add_mul_root d z, ?_⟩
  intro ab hab
  apply Prod.ext
  · simpa only [quadraticConstant_scalar_add_mul_root] using (congrArg (quadraticConstant d) hab).symm
  · simpa only [quadraticResidue_scalar_add_mul_root] using (congrArg (quadraticResidue d) hab).symm

/-- Monic division literally leaves the constant and linear coefficients. -/
theorem quadratic_remainder_eq (d : R) (g : R[X]) :
    g %ₘ quadraticPolynomial d = C ((g %ₘ quadraticPolynomial d).coeff 0) +
      C ((g %ₘ quadraticPolynomial d).coeff 1) * X := by
  have hd := degree_modByMonic_lt g (quadraticPolynomial_monic d)
  rw [degree_eq_natDegree (quadraticPolynomial_monic d).ne_zero,
    quadraticPolynomial_natDegree] at hd
  ext n
  by_cases hn0 : n = 0
  · subst n
    simp
  by_cases hn1 : n = 1
  · subst n
    simp
  have hn : 2 ≤ n := by omega
  have hc : (g %ₘ quadraticPolynomial d).coeff n = 0 :=
    coeff_eq_zero_of_degree_lt (hd.trans_le (by exact_mod_cast hn))
  simp [hc, coeff_C, coeff_X, hn0, Ne.symm hn1]

@[simp] theorem quadraticResidue_scalar (d a : R) :
    quadraticResidue d (algebraMap R (quadraticQuotient d) a) = 0 := by
  simpa only [map_zero, zero_mul, add_zero] using quadraticResidue_scalar_add_mul_root d a 0

@[simp] theorem quadraticResidue_one (d : R) : quadraticResidue d 1 = 0 := by
  simpa only [map_one] using quadraticResidue_scalar d 1

@[simp] theorem quadraticResidue_root (d : R) : quadraticResidue d (quadraticRoot d) = 1 := by
  simpa only [map_zero, map_one, one_mul, zero_add] using quadraticResidue_scalar_add_mul_root d 0 1

/-- The actual residue pairing is perfect, including at `d=0`. -/
def quadraticResiduePairingEquiv (d : R) :
    quadraticQuotient d ≃ₗ[R] Module.Dual R (quadraticQuotient d) :=
  residuePairingEquiv (quadraticPolynomial d) (quadraticPolynomial_monic d)

omit [Nontrivial R] in
@[simp] theorem quadraticResiduePairingEquiv_apply (d : R) (z w : quadraticQuotient d) :
    quadraticResiduePairingEquiv d z w = quadraticResidue d (z * w) := rfl

/-- The Gram matrix of the actual bilinear pairing in the basis `1,W`. -/
def quadraticResidueGram (d : R) : Matrix (Fin 2) (Fin 2) R :=
  fun i j => quadraticResidue d (quadraticBasis d i * quadraticBasis d j)

/-- The collision-independent matrix in `trigonometry:eq:pairmatrix`. -/
theorem quadraticResidueGram_eq (d : R) : quadraticResidueGram d = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change quadraticResidue d (quadraticBasis d 0 * quadraticBasis d 0) = 0
    rw [quadraticBasis_zero, one_mul, quadraticResidue_one]
  · change quadraticResidue d (quadraticBasis d 0 * quadraticBasis d 1) = 1
    rw [quadraticBasis_zero, quadraticBasis_one, one_mul, quadraticResidue_root]
  · change quadraticResidue d (quadraticBasis d 1 * quadraticBasis d 0) = 1
    rw [quadraticBasis_zero, quadraticBasis_one, mul_one, quadraticResidue_root]
  · change quadraticResidue d (quadraticBasis d 1 * quadraticBasis d 1) = 0
    rw [quadraticBasis_one, ← pow_two, quadraticRoot_sq, quadraticResidue_scalar]

/-- The residue determinant is the unit `-1` at every parameter. -/
theorem det_quadraticResidueGram (d : R) : (quadraticResidueGram d).det = -1 := by
  rw [quadraticResidueGram_eq, Matrix.det_fin_two]
  simp

omit [Nontrivial R] in
theorem quadratic_scalar_add_mul_root_mul_root (d a b : R) :
    (algebraMap R (quadraticQuotient d) a +
      algebraMap R (quadraticQuotient d) b * quadraticRoot d) * quadraticRoot d =
      algebraMap R (quadraticQuotient d) (b * d) +
        algebraMap R (quadraticQuotient d) a * quadraticRoot d := by
  rw [add_mul, mul_assoc, ← pow_two, quadraticRoot_sq, ← map_mul]
  exact add_comm _ _

/-- Multiplication by `a+bW` has the source's literal matrix, even at a double root. -/
theorem quadratic_leftMulMatrix (d a b : R) :
    Algebra.leftMulMatrix (quadraticBasis d)
      (algebraMap R (quadraticQuotient d) a +
        algebraMap R (quadraticQuotient d) b * quadraticRoot d) = !![a, b * d; b, a] := by
  ext i j
  simp only [Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases i <;> fin_cases j
  · change (quadraticBasis d).repr (_ * quadraticBasis d 0) 0 = a
    rw [quadraticBasis_zero, mul_one, ← quadraticConstant_eq_repr,
      quadraticConstant_scalar_add_mul_root]
  · change (quadraticBasis d).repr (_ * quadraticBasis d 1) 0 = b * d
    rw [quadraticBasis_one, quadratic_scalar_add_mul_root_mul_root,
      ← quadraticConstant_eq_repr, quadraticConstant_scalar_add_mul_root]
  · change (quadraticBasis d).repr (_ * quadraticBasis d 0) 1 = b
    rw [quadraticBasis_zero, mul_one, ← quadraticResidue_eq_repr,
      quadraticResidue_scalar_add_mul_root]
  · change (quadraticBasis d).repr (_ * quadraticBasis d 1) 1 = a
    rw [quadraticBasis_one, quadratic_scalar_add_mul_root_mul_root,
      ← quadraticResidue_eq_repr, quadraticResidue_scalar_add_mul_root]

/-- The trace of multiplication is twice the constant remainder coordinate. -/
theorem quadratic_trace (d : R) (z : quadraticQuotient d) :
    Algebra.trace R (quadraticQuotient d) z = 2 * quadraticConstant d z := by
  rw [Algebra.trace_eq_matrix_trace (quadraticBasis d)]
  conv_lhs => arg 1; rw [quadratic_eq_scalar_add_mul_root d z]
  rw [quadratic_leftMulMatrix, Matrix.trace, Fin.sum_univ_two]
  change quadraticConstant d z + quadraticConstant d z = 2 * quadraticConstant d z
  ring

omit [Nontrivial R] in
/-- The trace is the residue against the derivative `2W`, as stated in the manuscript. -/
theorem quadratic_trace_eq_residue (d : R) (z : quadraticQuotient d) :
    Algebra.trace R (quadraticQuotient d) z = quadraticResidue d (2 * quadraticRoot d * z) := by
  have hd : AdjoinRoot.mk (quadraticPolynomial d) (quadraticPolynomial d).derivative =
      2 * quadraticRoot d := by
    have hp : (quadraticPolynomial d).derivative = C (2 : R) * X := by
      norm_num [quadraticPolynomial, map_ofNat]
    rw [hp, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    change algebraMap R (quadraticQuotient d) 2 * quadraticRoot d = _
    rw [map_ofNat]
  simpa only [hd, quadraticResidue] using
    quotient_trace_eq_residue_derivative (quadraticPolynomial d) (quadraticPolynomial_monic d) z

end
end Surreal.FinitePolynomial
