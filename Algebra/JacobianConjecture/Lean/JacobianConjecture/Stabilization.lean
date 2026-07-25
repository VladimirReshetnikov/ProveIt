import JacobianConjecture.Counterexample
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Fin.Basic

/-!
# Stabilization: the Jacobian conjecture fails in every dimension ≥ 3

Adjoining `m` untouched coordinates to the three-variable counterexample
produces a polynomial self-map in dimension `3 + m` that still refutes the
Jacobian conjecture.  The stabilized map sends the first three coordinates
through Alpöge's map — with its polynomials renamed along the coordinate
inclusion `Fin 3 → Fin (3 + m)` — and fixes each of the remaining `m`
coordinates.

* Its Jacobian matrix is block lower triangular after splitting the index set
  as `Fin 3 ⊕ Fin m`: the top-left block is the renamed three-by-three
  Jacobian, the top-right block vanishes because the first three coordinate
  polynomials never mention the new variables, and the bottom-right block is
  the identity.  Hence the Jacobian determinant is still the constant `-2`.
* Padding the three-variable collision points with zeros in the new
  coordinates gives two distinct points with a common image, so the map has
  no set-theoretic left inverse.

Since every `n ≥ 3` has the form `3 + m`, the Jacobian conjecture is false in
every dimension at least three over every characteristic-zero field.
-/

namespace LeanProofs.JacobianStabilization

open Function Matrix MvPolynomial
open JacobianCounterexample
open JacobianCounterexample.PolynomialMap

universe u

/-- The three-variable counterexample with `m` untouched coordinates adjoined:
the first three coordinates are Alpöge's polynomials in the first three
variables, and each remaining coordinate is the corresponding variable. -/
noncomputable def stabilized (R : Type u) [CommRing R] (m : ℕ) :
    PolynomialMap (3 + m) R :=
  fun i =>
    Sum.elim
      (fun j => rename (Fin.castAdd m) (counterexample R j))
      (fun k => X (Fin.natAdd 3 k))
      (finSumFinEquiv.symm i)

theorem stabilized_castAdd (R : Type u) [CommRing R] (m : ℕ) (j : Fin 3) :
    stabilized R m (Fin.castAdd m j) =
      rename (Fin.castAdd m) (counterexample R j) := by
  simp [stabilized]

theorem stabilized_natAdd (R : Type u) [CommRing R] (m : ℕ) (k : Fin m) :
    stabilized R m (Fin.natAdd 3 k) = X (Fin.natAdd 3 k) := by
  simp [stabilized]

/-- On the original coordinates, the stabilized map evaluates through the
three-variable counterexample. -/
theorem evalMap_stabilized_castAdd (R : Type u) [CommRing R] (m : ℕ)
    (a : Fin (3 + m) → R) (j : Fin 3) :
    evalMap (stabilized R m) a (Fin.castAdd m j) =
      evalMap (counterexample R) (a ∘ Fin.castAdd m) j := by
  simp only [evalMap, stabilized_castAdd]
  rw [eval_rename]

/-- On the adjoined coordinates, the stabilized map is the identity. -/
theorem evalMap_stabilized_natAdd (R : Type u) [CommRing R] (m : ℕ)
    (a : Fin (3 + m) → R) (k : Fin m) :
    evalMap (stabilized R m) a (Fin.natAdd 3 k) = a (Fin.natAdd 3 k) := by
  simp [evalMap, stabilized_natAdd]

/-- Zero-pad a three-coordinate point to `3 + m` coordinates. -/
def padded {R : Type u} [CommRing R] (m : ℕ) (p : Fin 3 → R) :
    Fin (3 + m) → R :=
  Sum.elim p (fun _ => 0) ∘ finSumFinEquiv.symm

@[simp] theorem padded_castAdd {R : Type u} [CommRing R] (m : ℕ)
    (p : Fin 3 → R) (j : Fin 3) :
    padded m p (Fin.castAdd m j) = p j := by
  simp [padded]

@[simp] theorem padded_natAdd {R : Type u} [CommRing R] (m : ℕ)
    (p : Fin 3 → R) (k : Fin m) :
    padded m p (Fin.natAdd 3 k) = 0 := by
  simp [padded]

theorem padded_comp_castAdd {R : Type u} [CommRing R] (m : ℕ)
    (p : Fin 3 → R) : padded m p ∘ Fin.castAdd m = p :=
  funext fun j => padded_castAdd m p j

/-- The padded first collision point maps to the padded collision value. -/
theorem stabilized_collision₀_value (R : Type u) [CommRing R] (m : ℕ) :
    evalMap (stabilized R m) (padded m (collision₀ R)) =
      padded m (collisionValue R) := by
  funext i
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  cases s with
  | inl j =>
      rw [finSumFinEquiv_apply_left, evalMap_stabilized_castAdd,
        padded_comp_castAdd, padded_castAdd]
      exact congrFun (collision₀_value R) j
  | inr k =>
      rw [finSumFinEquiv_apply_right, evalMap_stabilized_natAdd,
        padded_natAdd, padded_natAdd]

/-- The padded second collision point maps to the padded collision value. -/
theorem stabilized_collision₁_value (R : Type u) [CommRing R] (m : ℕ) :
    evalMap (stabilized R m) (padded m (collision₁ R)) =
      padded m (collisionValue R) := by
  funext i
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  cases s with
  | inl j =>
      rw [finSumFinEquiv_apply_left, evalMap_stabilized_castAdd,
        padded_comp_castAdd, padded_castAdd]
      exact congrFun (collision₁_value R) j
  | inr k =>
      rw [finSumFinEquiv_apply_right, evalMap_stabilized_natAdd,
        padded_natAdd, padded_natAdd]

theorem stabilized_collision (R : Type u) [CommRing R] (m : ℕ) :
    evalMap (stabilized R m) (padded m (collision₀ R)) =
      evalMap (stabilized R m) (padded m (collision₁ R)) :=
  (stabilized_collision₀_value R m).trans
    (stabilized_collision₁_value R m).symm

theorem stabilized_collision_points_distinct
    (R : Type u) [CommRing R] [Nontrivial R] (m : ℕ) :
    padded m (collision₀ R) ≠ padded m (collision₁ R) := by
  intro h
  have h₀ := congrFun h (Fin.castAdd m 0)
  rw [padded_castAdd, padded_castAdd] at h₀
  simp [collision₀, collision₁] at h₀

/-!
## The Jacobian determinant

Splitting the coordinates as `Fin 3 ⊕ Fin m` exhibits the Jacobian matrix as
a block lower triangular matrix whose diagonal blocks are the renamed
three-variable Jacobian and the identity.
-/

/-- A renamed polynomial has vanishing formal partial derivative along every
variable outside the range of the renaming. -/
private theorem pderiv_rename_of_forall_ne {σ τ : Type*} {R : Type u}
    [CommSemiring R] {f : σ → τ} {j : τ} (h : ∀ k, f k ≠ j)
    (p : MvPolynomial σ R) :
    pderiv j (rename f p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp => simp [hp, pderiv_X_of_ne (h k)]

/-- Original and adjoined coordinate indices never coincide. -/
private theorem castAdd_ne_natAdd (m : ℕ) (t : Fin 3) (k : Fin m) :
    Fin.castAdd m t ≠ Fin.natAdd 3 k := by
  intro h
  have h' : (t : ℕ) = 3 + (k : ℕ) := congrArg Fin.val h
  have ht : (t : ℕ) < 3 := t.isLt
  omega

private abbrev splitEquiv (m : ℕ) : Fin (3 + m) ≃ Fin 3 ⊕ Fin m :=
  (@finSumFinEquiv 3 m).symm

private noncomputable def splitJacobian (R : Type u) [CommRing R] (m : ℕ) :
    Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) (MvPolynomial (Fin (3 + m)) R) :=
  Matrix.reindex (splitEquiv m) (splitEquiv m) (jacobian (stabilized R m))

private theorem splitJacobian_topLeft (R : Type u) [CommRing R] (m : ℕ) :
    (splitJacobian R m).toBlocks₁₁ =
      (jacobian (counterexample R)).map (rename (Fin.castAdd m)) := by
  funext i j
  simp only [splitJacobian, Matrix.toBlocks₁₁, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, finSumFinEquiv_apply_left,
    Matrix.map_apply, Matrix.of_apply, jacobian]
  rw [stabilized_castAdd, pderiv_rename (Fin.castAdd_injective 3 m)]

private theorem splitJacobian_topRight (R : Type u) [CommRing R] (m : ℕ) :
    (splitJacobian R m).toBlocks₁₂ = 0 := by
  funext i k
  simp only [splitJacobian, Matrix.toBlocks₁₂, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right, Matrix.of_apply, Matrix.zero_apply, jacobian]
  rw [stabilized_castAdd]
  exact pderiv_rename_of_forall_ne (fun t => castAdd_ne_natAdd m t k) _

private theorem splitJacobian_bottomRight (R : Type u) [CommRing R] (m : ℕ) :
    (splitJacobian R m).toBlocks₂₂ = 1 := by
  funext k l
  simp only [splitJacobian, Matrix.toBlocks₂₂, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, finSumFinEquiv_apply_right,
    Matrix.of_apply, jacobian, stabilized_natAdd]
  by_cases h : k = l
  · subst h
    rw [pderiv_X_self, Matrix.one_apply_eq]
  · have hne : Fin.natAdd 3 k ≠ Fin.natAdd 3 l :=
      fun hkl => h (Fin.natAdd_injective m 3 hkl)
    rw [pderiv_X_of_ne hne, Matrix.one_apply_ne h]

private theorem det_stabilized_eq_det_topLeft (R : Type u) [CommRing R]
    (m : ℕ) :
    (jacobian (stabilized R m)).det = (splitJacobian R m).toBlocks₁₁.det := by
  calc
    (jacobian (stabilized R m)).det = (splitJacobian R m).det :=
      (Matrix.det_reindex_self (splitEquiv m) (jacobian (stabilized R m))).symm
    _ = (splitJacobian R m).toBlocks₁₁.det :=
      det_eq_det_toBlocks₁₁ _ (splitJacobian_topRight R m) (splitJacobian_bottomRight R m)

/-- **Keller calculation, stabilized.** The formal Jacobian determinant of the
stabilized map is the constant polynomial `-2`, over every commutative ring
and in every dimension `3 + m`. -/
theorem jacobianDet_stabilized (R : Type u) [CommRing R] (m : ℕ) :
    jacobianDet (stabilized R m) = C (-2 : R) := by
  calc
    jacobianDet (stabilized R m) = (splitJacobian R m).toBlocks₁₁.det :=
      det_stabilized_eq_det_topLeft R m
    _ = ((jacobian (counterexample R)).map (rename (Fin.castAdd m))).det := by
      rw [splitJacobian_topLeft R m]
    _ = rename (Fin.castAdd m) (jacobianDet (counterexample R)) := by
      have h := AlgHom.map_det (rename (Fin.castAdd m))
        (jacobian (counterexample R))
      rw [AlgHom.mapMatrix_apply] at h
      exact h.symm
    _ = rename (Fin.castAdd m) (C (-2 : R)) := by
      rw [jacobianDet_counterexample R]
    _ = C (-2 : R) := rename_C _ _

/-!
## Refutation in every dimension at least three
-/

/-- The stabilized map is not injective over any nontrivial commutative
ring. -/
theorem stabilized_not_injective
    (R : Type u) [CommRing R] [Nontrivial R] (m : ℕ) :
    ¬ Injective (evalMap (stabilized R m)) := by
  intro h
  exact stabilized_collision_points_distinct R m (h (stabilized_collision R m))

/-- In characteristic zero the determinant `-2` is nonzero, so the stabilized
map satisfies the Keller condition. -/
theorem stabilized_has_nonzero_constant_jacobian
    (R : Type u) [Field R] [CharZero R] (m : ℕ) :
    HasNonzeroConstantJacobian (stabilized R m) :=
  ⟨-2, by norm_num, jacobianDet_stabilized R m⟩

/-- The padded collision rules out even a polynomial left inverse. -/
theorem stabilized_has_no_polynomial_inverse (R : Type u) [Field R] (m : ℕ) :
    ¬ HasPolynomialInverse (stabilized R m) := by
  rintro ⟨g, hleft, _⟩
  exact stabilized_not_injective R m hleft.injective

/-- **The Jacobian conjecture is false in every dimension at least three**
over every characteristic-zero field. -/
theorem jacobianConjectureInDimension_false_of_three_le
    (R : Type u) [Field R] [CharZero R] (n : ℕ) (hn : 3 ≤ n) :
    ¬ JacobianConjectureInDimension n R := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 3 + m := ⟨n - 3, by omega⟩
  intro h
  exact stabilized_has_no_polynomial_inverse R m
    (h (stabilized R m) (stabilized_has_nonzero_constant_jacobian R m))

/-- The classical complex Jacobian conjecture is false in every dimension at
least three. -/
theorem jacobianConjectureInDimension_false_of_three_le_over_complex
    (n : ℕ) (hn : 3 ≤ n) :
    ¬ JacobianConjectureInDimension n ℂ :=
  jacobianConjectureInDimension_false_of_three_le ℂ n hn

end LeanProofs.JacobianStabilization
