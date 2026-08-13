import PolynomialFormulas.LazardQuintic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Figure-3 invariant linear system

This module isolates the four-by-four coefficient matrix of Lazard's equations
for `i₅,…,i₈`.  A nonzero determinant is the exact algebraic boundary needed
to make those four equations determine the invariant tail uniquely.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

set_option autoImplicit false
set_option maxRecDepth 10000

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- Reassemble an invariant tuple from `i₄` and the tail `(i₅,i₆,i₇,i₈)`. -/
def Invariants.ofI4Tail (i4 : K) (tail : Fin 4 → K) : Invariants K :=
  ⟨i4, tail 0, tail 1, tail 2, tail 3⟩

/-- The tail `(i₅,i₆,i₇,i₈)` of an invariant tuple. -/
def Invariants.tail (i : Invariants K) : Fin 4 → K :=
  ![i.i5, i.i6, i.i7, i.i8]

omit [Field K] [CharZero K] in
@[simp] theorem Invariants.ofI4Tail_tail (i : Invariants K) :
    Invariants.ofI4Tail i.i4 i.tail = i := by
  cases i
  rfl

/-- The right sides of the four linear equations in Lazard's Figure 3. -/
def invariantSystemRhs (c : DepressedQuintic K) (i : Invariants K) : Fin 4 → K :=
  ![i4SquareRhs c i, i4CubeRhs c i, i4FourthRhs c i, i4FifthRhs c i]

/-- The homogeneous linear part of the Figure-3 right sides.  The `i₄` value
is set to zero because all dependence on it belongs to the affine constant
term, while the coefficients of `i₅,…,i₈` do not depend on `i₄`. -/
def invariantSystemLinear (c : DepressedQuintic K) (tail : Fin 4 → K) : Fin 4 → K :=
  invariantSystemRhs c (Invariants.ofI4Tail 0 tail) -
    invariantSystemRhs c (Invariants.ofI4Tail 0 0)

/-- The coefficient matrix of the four Figure-3 equations in the unknowns
`(i₅,i₆,i₇,i₈)`. -/
def invariantSystemMatrix (c : DepressedQuintic K) : Matrix (Fin 4) (Fin 4) K :=
  fun row col => invariantSystemLinear c (Pi.single col 1) row

theorem invariantSystemMatrix_mulVec (c : DepressedQuintic K) (tail : Fin 4 → K) :
    (invariantSystemMatrix c).mulVec tail = invariantSystemLinear c tail := by
  funext row
  fin_cases row <;>
    simp [invariantSystemMatrix, invariantSystemLinear, invariantSystemRhs,
      Invariants.ofI4Tail, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Pi.single_apply, i4SquareRhs, i4CubeRhs, i4FourthRhs, i4FifthRhs] <;>
    ring

/-- Split the affine Figure-3 right sides into their constant and linear
parts. -/
theorem invariantSystemRhs_eq (c : DepressedQuintic K) (i : Invariants K) :
    invariantSystemRhs c i =
      invariantSystemRhs c (Invariants.ofI4Tail i.i4 0) +
        (invariantSystemMatrix c).mulVec i.tail := by
  rw [invariantSystemMatrix_mulVec]
  funext row
  fin_cases row <;>
    simp [invariantSystemLinear, invariantSystemRhs, Invariants.ofI4Tail,
      Invariants.tail, i4SquareRhs, i4CubeRhs, i4FourthRhs, i4FifthRhs] <;>
    ring

/-- If the Figure-3 coefficient determinant is nonzero, its four equations
uniquely determine `i₅,…,i₈` once `i₄` is fixed. -/
theorem InvariantRelations.eq_of_i4_eq_of_det_ne_zero
    {c : DepressedQuintic K} {i j : Invariants K}
    (hi : InvariantRelations c i) (hj : InvariantRelations c j)
    (hi4 : i.i4 = j.i4) (hdet : (invariantSystemMatrix c).det ≠ 0) :
    i = j := by
  have hrhs : invariantSystemRhs c i = invariantSystemRhs c j := by
    funext row
    fin_cases row
    · exact hi.square.symm.trans (hi4 ▸ hj.square)
    · exact hi.cube.symm.trans (hi4 ▸ hj.cube)
    · exact hi.fourth.symm.trans (hi4 ▸ hj.fourth)
    · exact hi.fifth.symm.trans (hi4 ▸ hj.fifth)
  have hmul :
      (invariantSystemMatrix c).mulVec i.tail =
        (invariantSystemMatrix c).mulVec j.tail := by
    rw [invariantSystemRhs_eq c i, invariantSystemRhs_eq c j] at hrhs
    have hbase :
        invariantSystemRhs c (Invariants.ofI4Tail i.i4 0) =
          invariantSystemRhs c (Invariants.ofI4Tail j.i4 0) := by
      rw [hi4]
    rw [hbase] at hrhs
    exact add_left_cancel hrhs
  have hinj : Function.Injective (invariantSystemMatrix c).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  have htail : i.tail = j.tail := hinj hmul
  rw [← i.ofI4Tail_tail, ← j.ofI4Tail_tail, hi4, htail]

end Field

/-! ## A singular reducible specialization admitted by the raw interface -/

/-- The depressed quintic `X⁵ - X³ + 2X² + 3X + 1`. -/
def singularInvariantExample : DepressedQuintic ℚ := ⟨-1, 2, 3, 1⟩

/-- The example is reducible: it has the factor `X + 1`. -/
theorem singularInvariantExample_eval_factorization (x : ℚ) :
    singularInvariantExample.eval x =
      (x + 1) * (x ^ 4 - x ^ 3 + 2 * x + 1) := by
  simp [singularInvariantExample, DepressedQuintic.eval]
  ring

/-- Despite being reducible, the example has nonzero discriminant. -/
theorem singularInvariantExample_discriminant :
    discriminant singularInvariantExample = 189 := by
  norm_num [singularInvariantExample, discriminant]

/-- A radical-coherent member of the singular Figure-3 solution family. -/
def singularInvariantTuple : Invariants ℚ :=
  ⟨-4, -199 / 30, -79 / 30, 6, 109 / 15⟩

/-- A second member of the same Figure-3 solution family with the same `i₄`. -/
def singularInvariantTuple' : Invariants ℚ :=
  ⟨-4, -3, 1, 6, 0⟩

theorem singularInvariantTuple_relations :
    InvariantRelations singularInvariantExample singularInvariantTuple := by
  constructor <;>
    norm_num [singularInvariantExample, singularInvariantTuple, resolventEval,
      resolventCore, discriminant, i4SquareRhs, i4CubeRhs, i4FourthRhs,
      i4FifthRhs]

theorem singularInvariantTuple'_relations :
    InvariantRelations singularInvariantExample singularInvariantTuple' := by
  constructor <;>
    norm_num [singularInvariantExample, singularInvariantTuple', resolventEval,
      resolventCore, discriminant, i4SquareRhs, i4CubeRhs, i4FourthRhs,
      i4FifthRhs]

theorem singularInvariantTuple_ne : singularInvariantTuple ≠ singularInvariantTuple' := by
  intro h
  have := congrArg Invariants.i8 h
  norm_num [singularInvariantTuple, singularInvariantTuple'] at this

theorem singularInvariantSystem_det :
    (invariantSystemMatrix singularInvariantExample).det = 0 := by
  by_contra hdet
  apply singularInvariantTuple_ne
  exact singularInvariantTuple_relations.eq_of_i4_eq_of_det_ne_zero
    singularInvariantTuple'_relations (by rfl) hdet

/-- The extraneous tuple also passes the polynomial coherence identity behind
the two quadratic radical stages. -/
theorem singularInvariantTuple_radical_coherence :
    5 * invariantD singularInvariantExample singularInvariantTuple *
          invariantE singularInvariantExample singularInvariantTuple ^ 2 =
      invariantF singularInvariantExample singularInvariantTuple ^ 2 +
        4 * invariantG singularInvariantExample singularInvariantTuple ^ 2 := by
  norm_num [singularInvariantExample, singularInvariantTuple, invariantD,
    invariantE, invariantF, invariantG]

theorem singularInvariantTuple_D_ne_zero :
    invariantD singularInvariantExample singularInvariantTuple ≠ 0 := by
  norm_num [singularInvariantExample, singularInvariantTuple, invariantD]

theorem singularInvariantTuple_E_ne_zero :
    invariantE singularInvariantExample singularInvariantTuple ≠ 0 := by
  norm_num [singularInvariantExample, singularInvariantTuple, invariantE]

end LeanProofs.PolynomialFormulas.LazardQuintic
