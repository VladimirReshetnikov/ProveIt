import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The dimension-three Jacobian counterexample

This file states the Jacobian conjecture for polynomial maps over a field and
refutes both its dimension-three instance and the all-dimensions statement.
The witness is Alpöge's polynomial map

```text
((1+xy)^3 z + y^2 (1+xy) (4+3xy),
 y + 3x (1+xy)^2 z + 3xy^2 (4+3xy),
 2x - 3x^2y - x^3z).
```

Its *formal* multivariate-polynomial Jacobian has determinant `-2`, while the
two distinct integral points `(-1,1,5)` and `(0,-2,-16)` have the common image
`(0,-2,0)`.  Consequently the map has no set-theoretic left inverse and hence
no polynomial two-sided inverse.
-/

namespace LeanProofs.JacobianCounterexample

open Function Matrix MvPolynomial

universe u

/-- **Block lower-triangular determinant.**  A block matrix indexed by `m ⊕ n`
whose upper-right block vanishes and whose lower-right block is the identity
has determinant equal to that of its upper-left block.  Both the five-variable
and the stabilized determinant calculations reduce to this fact. -/
theorem det_eq_det_toBlocks₁₁ {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {R : Type u} [CommRing R]
    (M : Matrix (m ⊕ n) (m ⊕ n) R)
    (h₁₂ : M.toBlocks₁₂ = 0) (h₂₂ : M.toBlocks₂₂ = 1) :
    M.det = M.toBlocks₁₁.det := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M, h₁₂, h₂₂]
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

/-- An `n`-dimensional polynomial self-map over `R`. -/
abbrev PolynomialMap (n : Nat) (R : Type u) [CommSemiring R] :=
  Fin n → MvPolynomial (Fin n) R

namespace PolynomialMap

/-- Evaluate every coordinate polynomial of `f` at `a`. -/
noncomputable def evalMap {n : Nat} {R : Type u} [CommSemiring R]
    (f : PolynomialMap n R) (a : Fin n → R) : Fin n → R :=
  fun i => MvPolynomial.eval a (f i)

/-- The formal Jacobian matrix, with coordinate polynomials as rows. -/
noncomputable def jacobian {n : Nat} {R : Type u} [CommRing R]
    (f : PolynomialMap n R) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) R) :=
  fun i j => pderiv j (f i)

/-- The formal Jacobian determinant. -/
noncomputable def jacobianDet {n : Nat} {R : Type u} [CommRing R]
    (f : PolynomialMap n R) : MvPolynomial (Fin n) R :=
  (jacobian f).det

/-- The Keller condition: the formal Jacobian determinant is a nonzero
constant polynomial. -/
def HasNonzeroConstantJacobian {n : Nat} {R : Type u} [CommRing R]
    (f : PolynomialMap n R) : Prop :=
  ∃ c : R, c ≠ 0 ∧ jacobianDet f = C c

/-- A polynomial two-sided inverse, stated by its induced action on points. -/
def HasPolynomialInverse {n : Nat} {R : Type u} [CommSemiring R]
    (f : PolynomialMap n R) : Prop :=
  ∃ g : PolynomialMap n R,
    LeftInverse (evalMap g) (evalMap f) ∧ RightInverse (evalMap g) (evalMap f)

end PolynomialMap

open PolynomialMap

/-- The Jacobian conjecture over `R` in a fixed dimension. -/
def JacobianConjectureInDimension (n : Nat) (R : Type u) [Field R] : Prop :=
  ∀ f : PolynomialMap n R,
    HasNonzeroConstantJacobian f → HasPolynomialInverse f

/-- The Jacobian conjecture over `R` in all finite dimensions. -/
def JacobianConjecture (R : Type u) [Field R] : Prop :=
  ∀ n : Nat, JacobianConjectureInDimension n R

abbrev I := Fin 3

/-- Alpöge's three coordinate polynomials. -/
noncomputable def counterexample (R : Type u) [CommRing R] : PolynomialMap 3 R :=
  let x : MvPolynomial I R := X 0
  let y : MvPolynomial I R := X 1
  let z : MvPolynomial I R := X 2
  ![(1 + x * y) ^ 3 * z + y ^ 2 * (1 + x * y) * (4 + 3 * x * y),
    y + 3 * x * (1 + x * y) ^ 2 * z + 3 * x * y ^ 2 * (4 + 3 * x * y),
    2 * x - 3 * x ^ 2 * y - x ^ 3 * z]

/-- The usual closed formula for a three-by-three determinant. -/
private def det3 {R : Type u} [CommRing R] (A : Matrix I I R) : R :=
  A 0 0 * (A 1 1 * A 2 2 - A 1 2 * A 2 1) -
  A 0 1 * (A 1 0 * A 2 2 - A 1 2 * A 2 0) +
  A 0 2 * (A 1 0 * A 2 1 - A 1 1 * A 2 0)

private theorem det3_eq_det {R : Type u} [CommRing R] (A : Matrix I I R) :
    det3 A = A.det := by
  rw [Matrix.det_fin_three]
  simp only [det3]
  ring

/-- Numeric literals have vanishing formal partial derivatives.  Shared by
the determinant calculations of this file and `SimplerCounterexample`. -/
theorem pderiv_ofNat {σ R : Type*} [CommSemiring R] {i : σ} (n : Nat)
    [n.AtLeastTwo] :
    pderiv i (ofNat(n) : MvPolynomial σ R) = 0 := by
  rw [← map_ofNat (C : R →+* MvPolynomial σ R) n]
  exact pderiv_C

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8000 in
private theorem det3_jacobian_counterexample (R : Type u) [CommRing R] :
    det3 (jacobian (counterexample R)) =
      (-2 : MvPolynomial I R) := by
  classical
  simp [det3, jacobian, counterexample, pderiv_ofNat]
  ring

/-- **Keller calculation.** The formal Jacobian determinant is the constant
polynomial `-2`, over every commutative ring. -/
theorem jacobianDet_counterexample (R : Type u) [CommRing R] :
    jacobianDet (counterexample R) = C (-2 : R) := by
  calc
    jacobianDet (counterexample R) = det3 (jacobian (counterexample R)) :=
      (det3_eq_det _).symm
    _ = (-2 : MvPolynomial I R) := det3_jacobian_counterexample R
    _ = C (-2 : R) := by rw [map_neg, map_ofNat]

/-- First point in the denominator-free collision. -/
def collision₀ (R : Type u) [CommRing R] : I → R := ![-1, 1, 5]

/-- Second point in the denominator-free collision. -/
def collision₁ (R : Type u) [CommRing R] : I → R := ![0, -2, -16]

/-- The common image of `collision₀` and `collision₁`. -/
def collisionValue (R : Type u) [CommRing R] : I → R := ![0, -2, 0]

theorem collision₀_value (R : Type u) [CommRing R] :
    evalMap (counterexample R) (collision₀ R) = collisionValue R := by
  funext i
  fin_cases i <;>
    norm_num [evalMap, counterexample, collision₀, collisionValue,
      Matrix.cons_val_two]

theorem collision₁_value (R : Type u) [CommRing R] :
    evalMap (counterexample R) (collision₁ R) = collisionValue R := by
  funext i
  fin_cases i <;>
    norm_num [evalMap, counterexample, collision₁, collisionValue,
      Matrix.cons_val_two]

theorem collision (R : Type u) [CommRing R] :
    evalMap (counterexample R) (collision₀ R) =
      evalMap (counterexample R) (collision₁ R) :=
  (collision₀_value R).trans (collision₁_value R).symm

theorem collision_points_distinct (R : Type u) [CommRing R] [Nontrivial R] :
    collision₀ R ≠ collision₁ R := by
  intro h
  have h₀ := congrFun h 0
  simp [collision₀, collision₁] at h₀

/-- The displayed polynomial map is not injective over any nontrivial
commutative ring. -/
theorem counterexample_not_injective
    (R : Type u) [CommRing R] [Nontrivial R] :
    ¬ Injective (evalMap (counterexample R)) := by
  intro h
  exact collision_points_distinct R (h (collision R))

/-- In characteristic zero the determinant `-2` is nonzero, so the map
satisfies the Keller condition. -/
theorem counterexample_has_nonzero_constant_jacobian
    (R : Type u) [Field R] [CharZero R] :
    HasNonzeroConstantJacobian (counterexample R) := by
  refine ⟨-2, by norm_num, ?_⟩
  exact jacobianDet_counterexample R

/-- The collision rules out even a polynomial left inverse. -/
theorem counterexample_has_no_polynomial_inverse
    (R : Type u) [Field R] :
    ¬ HasPolynomialInverse (counterexample R) := by
  rintro ⟨g, hleft, _⟩
  exact counterexample_not_injective R hleft.injective

/-- **The Jacobian conjecture is false in dimension three** over every
characteristic-zero field. -/
theorem jacobianConjectureInDimensionThree_false
    (R : Type u) [Field R] [CharZero R] :
    ¬ JacobianConjectureInDimension 3 R := by
  intro h
  exact counterexample_has_no_polynomial_inverse R
    (h (counterexample R) (counterexample_has_nonzero_constant_jacobian R))

/-- The all-dimensions Jacobian conjecture is false over every
characteristic-zero field. -/
theorem jacobianConjecture_false
    (R : Type u) [Field R] [CharZero R] :
    ¬ JacobianConjecture R := by
  intro h
  exact jacobianConjectureInDimensionThree_false R (h 3)

/-- The classical complex Jacobian conjecture is false. -/
theorem jacobianConjecture_false_over_complex :
    ¬ JacobianConjecture ℂ :=
  jacobianConjecture_false ℂ

end LeanProofs.JacobianCounterexample
