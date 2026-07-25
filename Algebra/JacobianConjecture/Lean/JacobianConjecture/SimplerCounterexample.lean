import JacobianConjecture.Counterexample
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Matrix.Block

/-!
# A lower-degree stable Jacobian counterexample

The three-variable counterexample has ordinary degree seven. Introduce two
variables `a,b`, put `p = xy²`, `q = x²yz`, `U = a+p`, and `V = b+q`, and
replace `(P,Q,R)` by `(P-UV,Q,R,U,V)`. The degree-seven term `x³y³z` in
`P` cancels `pq`, leaving a degree-six five-variable map. Its Jacobian
determinant is still `-2`, and `(-1,1,5,1,-5)` and `(0,-2,-16,0,0)` both
map to `(0,-2,0,0,0)`.

The determinant proof is structural: add `V` times row four and `U` times
row five to the first Jacobian row. The result is block lower triangular,
with the old three-by-three Jacobian and the two-by-two identity on its
diagonal.
-/

namespace LeanProofs.JacobianSimplerCounterexample

open Function Matrix MvPolynomial
open JacobianCounterexample
open JacobianCounterexample.PolynomialMap

universe u

abbrev I5 := Fin 5
abbrev I3 := Fin 3

noncomputable def factorP (R : Type u) [CommRing R] : MvPolynomial I5 R :=
  X 0 * X 1 ^ 2

noncomputable def factorQ (R : Type u) [CommRing R] : MvPolynomial I5 R :=
  X 0 ^ 2 * X 1 * X 2

noncomputable def sourceA (R : Type u) [CommRing R] : MvPolynomial I5 R :=
  X 3 + factorP R

noncomputable def sourceB (R : Type u) [CommRing R] : MvPolynomial I5 R :=
  X 4 + factorQ R

noncomputable def baseP (R : Type u) [CommRing R] : MvPolynomial I5 R :=
  (1 + X 0 * X 1) ^ 3 * X 2 +
    X 1 ^ 2 * (1 + X 0 * X 1) * (4 + 3 * X 0 * X 1)

noncomputable def baseQ (R : Type u) [CommRing R] : MvPolynomial I5 R :=
  X 1 + 3 * X 0 * (1 + X 0 * X 1) ^ 2 * X 2 +
    3 * X 0 * X 1 ^ 2 * (4 + 3 * X 0 * X 1)

noncomputable def baseR (R : Type u) [CommRing R] : MvPolynomial I5 R :=
  2 * X 0 - 3 * X 0 ^ 2 * X 1 - X 0 ^ 3 * X 2

/-- Expanded first coordinate, with no monomial above degree six. -/
noncomputable def simplerFirst (R : Type u) [CommRing R] : MvPolynomial I5 R :=
  -(X 3 * X 4) - X 3 * factorQ R - X 4 * factorP R +
    3 * X 0 ^ 2 * X 1 ^ 4 + 3 * X 0 ^ 2 * X 1 ^ 2 * X 2 +
    7 * X 0 * X 1 ^ 3 + 3 * X 0 * X 1 * X 2 + 4 * X 1 ^ 2 + X 2

/-- The five-variable degree-six stable counterexample. -/
noncomputable def simplerCounterexample (R : Type u) [CommRing R] :
    PolynomialMap 5 R :=
  ![simplerFirst R, baseQ R, baseR R, sourceA R, sourceB R]

/-- A tiny expression language used to certify ordinary-degree bounds without
depending on the internal sparse representation of `MvPolynomial`. -/
inductive DegreeExpr (R : Type u) where
  | constant : R → DegreeExpr R
  | var : I5 → DegreeExpr R
  | add : DegreeExpr R → DegreeExpr R → DegreeExpr R
  | mul : DegreeExpr R → DegreeExpr R → DegreeExpr R
  | neg : DegreeExpr R → DegreeExpr R

namespace DegreeExpr

noncomputable def toPolynomial {R : Type u} [CommRing R] :
    DegreeExpr R → MvPolynomial I5 R
  | .constant c => C c
  | .var i => X i
  | .add p q => toPolynomial p + toPolynomial q
  | .mul p q => toPolynomial p * toPolynomial q
  | .neg p => -toPolynomial p

/-- The usual syntax-directed upper bound for total degree. -/
def degreeBound {R : Type u} : DegreeExpr R → Nat
  | .constant _ => 0
  | .var _ => 1
  | .add p q => max (degreeBound p) (degreeBound q)
  | .mul p q => degreeBound p + degreeBound q
  | .neg p => degreeBound p

theorem totalDegree_toPolynomial_le {R : Type u} [CommRing R] [Nontrivial R]
    (e : DegreeExpr R) :
    (toPolynomial e).totalDegree ≤ degreeBound e := by
  induction e with
  | constant c => simp [toPolynomial, degreeBound]
  | var i => simp [toPolynomial, degreeBound]
  | add p q hp hq =>
      exact (totalDegree_add _ _).trans (max_le_max hp hq)
  | mul p q hp hq =>
      exact (totalDegree_mul _ _).trans (Nat.add_le_add hp hq)
  | neg p hp => simpa [toPolynomial, degreeBound, totalDegree_neg] using hp

end DegreeExpr

/-- Reified syntax for the five displayed coordinates.  The first coordinate
is deliberately expanded, so its cancelled degree-seven term is absent. -/
noncomputable def degreeExpressions (R : Type u) [CommRing R] :
    I5 → DegreeExpr R :=
  let c (n : Nat) : DegreeExpr R := .constant n
  let x : DegreeExpr R := .var 0
  let y : DegreeExpr R := .var 1
  let z : DegreeExpr R := .var 2
  let a : DegreeExpr R := .var 3
  let b : DegreeExpr R := .var 4
  let add := DegreeExpr.add
  let mul := DegreeExpr.mul
  let neg := DegreeExpr.neg
  let sq (t : DegreeExpr R) := mul t t
  let cube (t : DegreeExpr R) := mul (sq t) t
  let fourth (t : DegreeExpr R) := sq (sq t)
  let p := mul x (sq y)
  let q := mul (mul (sq x) y) z
  let u := add (c 1) (mul x y)
  ![
    add (neg (mul a b))
      (add (neg (mul a q))
        (add (neg (mul b p))
          (add (mul (c 3) (mul (sq x) (fourth y)))
            (add (mul (c 3) (mul (mul (sq x) (sq y)) z))
              (add (mul (c 7) (mul x (cube y)))
                (add (mul (c 3) (mul (mul x y) z))
                  (add (mul (c 4) (sq y)) z))))))),
    add y
      (add (mul (mul (c 3) x) (mul (sq u) z))
        (mul (mul (mul (c 3) x) (sq y))
          (add (c 4) (mul (c 3) (mul x y))))),
    add (add (mul (c 2) x) (neg (mul (mul (c 3) (sq x)) y)))
      (neg (mul (cube x) z)),
    add a p,
    add b q]

/-- The syntax-directed coordinate degree profile is `(6,6,4,3,4)`. -/
theorem degreeExpressions_profile (R : Type u) [CommRing R] :
    (fun i => DegreeExpr.degreeBound (degreeExpressions R i)) = ![6, 6, 4, 3, 4] := by
  funext i
  fin_cases i <;> rfl

set_option maxHeartbeats 800000 in
theorem degreeExpressions_toPolynomial (R : Type u) [CommRing R] :
    (fun i => DegreeExpr.toPolynomial (degreeExpressions R i)) =
      simplerCounterexample R := by
  funext i
  fin_cases i <;>
    simp [degreeExpressions, DegreeExpr.toPolynomial, simplerCounterexample,
      simplerFirst, baseQ, baseR, sourceA, sourceB, factorP, factorQ,
      map_ofNat] <;>
    ring

/-- Consequently, the actual total degrees of the five coordinates are
bounded coordinatewise by `(6,6,4,3,4)`. -/
theorem simplerCounterexample_totalDegree_le_profile
    (R : Type u) [CommRing R] [Nontrivial R] (i : I5) :
    (simplerCounterexample R i).totalDegree ≤ ![6, 6, 4, 3, 4] i := by
  calc
    (simplerCounterexample R i).totalDegree =
        (DegreeExpr.toPolynomial (degreeExpressions R i)).totalDegree :=
      congrArg MvPolynomial.totalDegree
        (congrFun (degreeExpressions_toPolynomial R) i).symm
    _ ≤ DegreeExpr.degreeBound (degreeExpressions R i) :=
      DegreeExpr.totalDegree_toPolynomial_le _
    _ = ![6, 6, 4, 3, 4] i := congrFun (degreeExpressions_profile R) i

/-- In particular, the stable counterexample has ordinary degree at most six. -/
theorem simplerCounterexample_totalDegree_le_six
    (R : Type u) [CommRing R] [Nontrivial R] (i : I5) :
    (simplerCounterexample R i).totalDegree ≤ 6 := by
  have h := simplerCounterexample_totalDegree_le_profile R i
  fin_cases i <;> norm_num at h ⊢ <;> omega

/-- The expanded coordinate is exactly `P - (a+p)(b+q)`. -/
theorem simplerFirst_stable_identity (R : Type u) [CommRing R] :
    simplerFirst R = baseP R - sourceA R * sourceB R := by
  simp [simplerFirst, baseP, sourceA, sourceB, factorP, factorQ]
  ring

private noncomputable def rowReducedJacobian (R : Type u) [CommRing R] :
    Matrix I5 I5 (MvPolynomial I5 R) :=
  let A := jacobian (simplerCounterexample R)
  let A₁ := A.updateRow 0 (A 0 + sourceB R • A 3)
  A₁.updateRow 0 (A₁ 0 + sourceA R • A₁ 4)

private theorem det_jacobian_eq_det_rowReduced (R : Type u) [CommRing R] :
    (jacobian (simplerCounterexample R)).det = (rowReducedJacobian R).det := by
  let A := jacobian (simplerCounterexample R)
  let A₁ := A.updateRow 0 (A 0 + sourceB R • A 3)
  have h₁ : A₁.det = A.det :=
    Matrix.det_updateRow_add_smul_self A (by decide : (0 : I5) ≠ 3) (sourceB R)
  have h₂ : (A₁.updateRow 0 (A₁ 0 + sourceA R • A₁ 4)).det = A₁.det :=
    Matrix.det_updateRow_add_smul_self A₁ (by decide : (0 : I5) ≠ 4) (sourceA R)
  exact h₁.symm.trans h₂.symm

private abbrev splitEquiv : I5 ≃ I3 ⊕ Fin 2 := (@finSumFinEquiv 3 2).symm

private noncomputable def splitReduced (R : Type u) [CommRing R] :
    Matrix (I3 ⊕ Fin 2) (I3 ⊕ Fin 2) (MvPolynomial I5 R) :=
  Matrix.reindex splitEquiv splitEquiv (rowReducedJacobian R)

set_option maxHeartbeats 800000 in
private theorem splitReduced_topRight (R : Type u) [CommRing R] :
    (splitReduced R).toBlocks₁₂ = 0 := by
  classical
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitReduced, splitEquiv, Matrix.toBlocks₁₂, rowReducedJacobian,
      Matrix.updateRow_apply, JacobianCounterexample.PolynomialMap.jacobian,
      simplerCounterexample, simplerFirst, baseQ, baseR, sourceA, sourceB,
      factorP, factorQ, pderiv_ofNat, finSumFinEquiv]

set_option maxHeartbeats 800000 in
private theorem splitReduced_bottomRight (R : Type u) [CommRing R] :
    (splitReduced R).toBlocks₂₂ = 1 := by
  classical
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitReduced, splitEquiv, Matrix.toBlocks₂₂, rowReducedJacobian,
      Matrix.updateRow_apply, JacobianCounterexample.PolynomialMap.jacobian,
      simplerCounterexample, simplerFirst, baseQ, baseR, sourceA, sourceB,
      factorP, factorQ, pderiv_ofNat, finSumFinEquiv]

private theorem det_rowReduced_eq_det_topLeft (R : Type u) [CommRing R] :
    (rowReducedJacobian R).det = (splitReduced R).toBlocks₁₁.det := by
  calc
    (rowReducedJacobian R).det = (splitReduced R).det :=
      (Matrix.det_reindex_self splitEquiv (rowReducedJacobian R)).symm
    _ = (splitReduced R).toBlocks₁₁.det :=
      det_eq_det_toBlocks₁₁ _ (splitReduced_topRight R) (splitReduced_bottomRight R)

private noncomputable def baseMap (R : Type u) [CommRing R] :
    I3 → MvPolynomial I5 R := ![baseP R, baseQ R, baseR R]

private noncomputable def baseJacobian (R : Type u) [CommRing R] :
    Matrix I3 I3 (MvPolynomial I5 R) :=
  fun i j ↦ pderiv (Fin.castAdd 2 j) (baseMap R i)

set_option maxHeartbeats 1200000 in
private theorem splitReduced_topLeft (R : Type u) [CommRing R] :
    (splitReduced R).toBlocks₁₁ = baseJacobian R := by
  classical
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitReduced, splitEquiv, Matrix.toBlocks₁₁, rowReducedJacobian,
      Matrix.updateRow_apply, JacobianCounterexample.PolynomialMap.jacobian,
      simplerCounterexample, simplerFirst, baseJacobian, baseMap, baseP, baseQ,
      baseR, sourceA, sourceB, factorP, factorQ, pderiv_ofNat, finSumFinEquiv] <;>
    ring

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8000 in
private theorem det_baseJacobian (R : Type u) [CommRing R] :
    (baseJacobian R).det = (-2 : MvPolynomial I5 R) := by
  classical
  rw [Matrix.det_fin_three]
  simp [baseJacobian, baseMap, baseP, baseQ, baseR, pderiv_ofNat]
  ring

/-- The formal five-by-five Jacobian determinant is the constant `-2`. -/
theorem jacobianDet_simplerCounterexample (R : Type u) [CommRing R] :
    jacobianDet (simplerCounterexample R) = C (-2 : R) := by
  calc
    jacobianDet (simplerCounterexample R) =
        (jacobian (simplerCounterexample R)).det := rfl
    _ = (rowReducedJacobian R).det := det_jacobian_eq_det_rowReduced R
    _ = (splitReduced R).toBlocks₁₁.det := det_rowReduced_eq_det_topLeft R
    _ = (baseJacobian R).det := by rw [splitReduced_topLeft R]
    _ = (-2 : MvPolynomial I5 R) := det_baseJacobian R
    _ = C (-2 : R) := by rw [map_neg, map_ofNat]

def collision₀ (R : Type u) [CommRing R] : I5 → R := ![-1, 1, 5, 1, -5]
def collision₁ (R : Type u) [CommRing R] : I5 → R := ![0, -2, -16, 0, 0]
def collisionValue (R : Type u) [CommRing R] : I5 → R := ![0, -2, 0, 0, 0]

set_option maxHeartbeats 800000 in
theorem collision₀_value (R : Type u) [CommRing R] :
    evalMap (simplerCounterexample R) (collision₀ R) = collisionValue R := by
  funext i
  fin_cases i <;>
    norm_num [evalMap, simplerCounterexample, simplerFirst, baseQ, baseR,
      sourceA, sourceB, factorP, factorQ, collision₀, collisionValue,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

set_option maxHeartbeats 800000 in
theorem collision₁_value (R : Type u) [CommRing R] :
    evalMap (simplerCounterexample R) (collision₁ R) = collisionValue R := by
  funext i
  fin_cases i <;>
    norm_num [evalMap, simplerCounterexample, simplerFirst, baseQ, baseR,
      sourceA, sourceB, factorP, factorQ, collision₁, collisionValue,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

theorem collision (R : Type u) [CommRing R] :
    evalMap (simplerCounterexample R) (collision₀ R) =
      evalMap (simplerCounterexample R) (collision₁ R) :=
  (collision₀_value R).trans (collision₁_value R).symm

theorem collision_points_distinct (R : Type u) [CommRing R] [Nontrivial R] :
    collision₀ R ≠ collision₁ R := by
  intro h
  have h₀ := congrFun h 0
  simp [collision₀, collision₁] at h₀

theorem simplerCounterexample_not_injective
    (R : Type u) [CommRing R] [Nontrivial R] :
    ¬ Injective (evalMap (simplerCounterexample R)) := by
  intro h
  exact collision_points_distinct R (h (collision R))

theorem simplerCounterexample_has_nonzero_constant_jacobian
    (R : Type u) [Field R] [CharZero R] :
    HasNonzeroConstantJacobian (simplerCounterexample R) := by
  refine ⟨-2, by norm_num, jacobianDet_simplerCounterexample R⟩

theorem simplerCounterexample_has_no_polynomial_inverse
    (R : Type u) [Field R] :
    ¬ HasPolynomialInverse (simplerCounterexample R) := by
  rintro ⟨g, hleft, _⟩
  exact simplerCounterexample_not_injective R hleft.injective

/-- The degree-six witness refutes the conjecture in dimension five. -/
theorem jacobianConjectureInDimensionFive_false
    (R : Type u) [Field R] [CharZero R] :
    ¬ JacobianConjectureInDimension 5 R := by
  intro h
  exact simplerCounterexample_has_no_polynomial_inverse R
    (h (simplerCounterexample R)
      (simplerCounterexample_has_nonzero_constant_jacobian R))

theorem jacobianConjectureInDimensionFive_false_over_complex :
    ¬ JacobianConjectureInDimension 5 ℂ :=
  jacobianConjectureInDimensionFive_false ℂ

/-!
## Equivariance

The triangular shears preserve the symmetry of the three-variable witness:
negating `x, y, a, b` in the source negates every image coordinate except the
first.  Mirroring the collision through this symmetry yields a second integral
collision with no new polynomial evaluation.
-/

/-- The source involution `(x, y, z, a, b) ↦ (-x, -y, z, -a, -b)`. -/
def flipSource5 {R : Type u} [CommRing R] (p : I5 → R) : I5 → R :=
  ![-p 0, -p 1, p 2, -p 3, -p 4]

/-- The target involution `(v₀, …, v₄) ↦ (v₀, -v₁, -v₂, -v₃, -v₄)`. -/
def flipTarget5 {R : Type u} [CommRing R] (v : I5 → R) : I5 → R :=
  ![v 0, -v 1, -v 2, -v 3, -v 4]

set_option maxHeartbeats 1600000 in
/-- **Equivariance of the stable counterexample.** -/
theorem simplerCounterexample_equivariant
    (R : Type u) [CommRing R] (p : I5 → R) :
    evalMap (simplerCounterexample R) (flipSource5 p) =
      flipTarget5 (evalMap (simplerCounterexample R) p) := by
  funext i
  fin_cases i <;>
    simp [evalMap, simplerCounterexample, simplerFirst, baseQ, baseR,
      sourceA, sourceB, factorP, factorQ, flipSource5, flipTarget5] <;>
    ring

/-- Mirroring the integral collision yields another one, with no new
polynomial evaluation. -/
theorem mirrored_collision (R : Type u) [CommRing R] :
    evalMap (simplerCounterexample R) (flipSource5 (collision₀ R)) =
      evalMap (simplerCounterexample R) (flipSource5 (collision₁ R)) := by
  rw [simplerCounterexample_equivariant, simplerCounterexample_equivariant,
    collision₀_value, collision₁_value]

end LeanProofs.JacobianSimplerCounterexample
