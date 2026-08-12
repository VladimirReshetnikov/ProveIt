import PolynomialFormulas.LazardInvariantOrderedRoots
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Iterating the ordered-root power bases

This file composes the rank-`n + 1` one-factor basis with the basis from the
preceding stage.  The crucial square is the polynomial base-change pushout

```
Aₙ  →  Aₙ[t]
↓        ↓
Eₙ  →  Eₙ[t],
```

where `Aₙ` is the generic coefficient ring and `Eₙ` is the ordered-root ring.
Thus an `Aₙ`-basis of `Eₙ` base-changes to an `Aₙ[t]`-basis of `Eₙ[t]`.
Composing it with the one-factor basis gives the next ordered-root basis.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantOrderedRootBasis

open scoped Polynomial TensorProduct
open Polynomial

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

variable (R : Type*) [CommRing R] [IsDomain R]

open LazardInvariantOrderedRoots

/-- The nested product index supplied by the successive power bases. -/
@[reducible] def TowerIndex : ℕ → Type
  | 0 => Unit
  | n + 1 => Fin (n + 1) × TowerIndex n

instance towerIndexFintype : (n : ℕ) → Fintype (TowerIndex n)
  | 0 => by
      change Fintype Unit
      infer_instance
  | n + 1 => by
      change Fintype (Fin (n + 1) × TowerIndex n)
      letI := towerIndexFintype n
      infer_instance

local instance orderedRootAlgebra (n : ℕ) :
    Algebra (CoefficientRing R n) (OrderedRootRing R n) :=
  (orderedCoefficientMap R n).toAlgebra

local instance polynomialFactorAlgebra (n : ℕ) :
    Algebra (CoefficientRing R (n + 1)) (FactorCoefficientRing R n) :=
  (polynomialFactorCoefficientMap R n).toAlgebra

local instance linearFactorCoefficientAlgebra (n : ℕ) :
    Algebra (CoefficientRing R (n + 1))
      (LazardInvariantLinearFactorBasis.LinearFactorRing R n) :=
  (LazardInvariantLinearFactorBasis.linearFactorCoefficientMap R n).toAlgebra

/-- Reassociation of the tensor presentation, now over the full generic
degree-`n + 1` coefficient ring. -/
def linearFactorPolynomialCoefficientEquiv (n : ℕ) :
    LazardInvariantLinearFactorBasis.LinearFactorRing R n ≃ₐ[CoefficientRing R (n + 1)]
      FactorCoefficientRing R n where
  __ := linearFactorPolynomialEquiv R n
  commutes' _ := rfl

/-- The one-step rank-`n + 1` basis in polynomial form. -/
def polynomialFactorBasis (n : ℕ) :
    Module.Basis (Fin (n + 1)) (CoefficientRing R (n + 1))
      (FactorCoefficientRing R n) :=
  (LazardInvariantLinearFactorBasis.linearFactorBasis R n).map
    (linearFactorPolynomialCoefficientEquiv R n).toLinearEquiv

@[simp]
theorem linearFactorPolynomialEquiv_distinguishedRoot (n : ℕ) :
    linearFactorPolynomialEquiv R n
        (LazardInvariantLinearFactorBasis.distinguishedRoot R n) =
      -MvPolynomial.X (0 : Fin 1) := by
  simp [linearFactorPolynomialEquiv,
    LazardInvariantLinearFactorBasis.distinguishedRoot,
    LazardInvariantLinearFactorBasis.linearCoefficient]

@[simp]
theorem polynomialFactorBasis_apply (n : ℕ) (i : Fin (n + 1)) :
    polynomialFactorBasis R n i =
      (-MvPolynomial.X (0 : Fin 1)) ^ (i : ℕ) := by
  rw [polynomialFactorBasis, Module.Basis.map_apply,
    LazardInvariantLinearFactorBasis.linearFactorBasis_apply]
  change (linearFactorPolynomialCoefficientEquiv R n)
    (LazardInvariantLinearFactorBasis.distinguishedRoot R n ^ (i : ℕ)) = _
  rw [map_pow]
  change (linearFactorPolynomialEquiv R n
    (LazardInvariantLinearFactorBasis.distinguishedRoot R n)) ^ (i : ℕ) = _
  rw [linearFactorPolynomialEquiv_distinguishedRoot]

/-- The coefficient map from the preceding generic coefficient ring into the
unflattened next ordered-root ring. -/
def factorOrderedBaseMap (n : ℕ) :
    CoefficientRing R n →ₐ[R] FactorOrderedRing R n :=
  (IsScalarTower.toAlgHom R (OrderedRootRing R n) (FactorOrderedRing R n)).comp
    (orderedCoefficientMap R n)

local instance factorOrderedBaseAlgebra (n : ℕ) :
    Algebra (CoefficientRing R n) (FactorOrderedRing R n) :=
  inferInstance

local instance factorPolynomialAlgebra (n : ℕ) :
    Algebra (FactorCoefficientRing R n) (FactorOrderedRing R n) :=
  MvPolynomial.algebraMvPolynomial

local instance coefficientOrderedScalarTower (n : ℕ) :
    IsScalarTower (CoefficientRing R n) (OrderedRootRing R n)
      (FactorOrderedRing R n) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance coefficientFactorScalarTower (n : ℕ) :
    IsScalarTower (CoefficientRing R n) (FactorCoefficientRing R n)
      (FactorOrderedRing R n) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    change MvPolynomial.C (orderedCoefficientMap R n x) =
      MvPolynomial.map (orderedCoefficientMap R n) (MvPolynomial.C x)
    simp

/-- The full generic degree-`n + 1` coefficient map before flattening. -/
def factorOrderedCoefficientMap (n : ℕ) :
    CoefficientRing R (n + 1) →ₐ[R] FactorOrderedRing R n :=
  (MvPolynomial.mapAlgHom (orderedCoefficientMap R n)).comp
    (polynomialFactorCoefficientMap R n)

local instance factorOrderedAlgebra (n : ℕ) :
    Algebra (CoefficientRing R (n + 1)) (FactorOrderedRing R n) :=
  (factorOrderedCoefficientMap R n).toAlgebra

local instance factorOrderedScalarTower (n : ℕ) :
    IsScalarTower (CoefficientRing R (n + 1))
      (FactorCoefficientRing R n) (FactorOrderedRing R n) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Flattening the nested polynomial ring respects the recursive generic
coefficient map. -/
def polynomialSuccCoefficientEquiv (n : ℕ) :
    FactorOrderedRing R n ≃ₐ[CoefficientRing R (n + 1)]
      OrderedRootRing R (n + 1) where
  __ := polynomialSuccEquiv R n
  commutes' _ := rfl

/-- The tagged empty ordered-root ring is the generic degree-zero coefficient
ring, as an algebra over that coefficient ring. -/
def orderedRootZeroCoefficientEquiv :
    CoefficientRing R 0 ≃ₐ[CoefficientRing R 0] OrderedRootRing R 0 where
  __ := (orderedRootPolynomialEquiv R 0).symm
  commutes' _ := rfl

/-- The basis obtained by iterating the honest one-factor power basis. -/
def orderedRootBasis : (n : ℕ) →
    Module.Basis (TowerIndex n) (CoefficientRing R n) (OrderedRootRing R n)
  | 0 =>
      (Module.Basis.singleton Unit (CoefficientRing R 0)).map
        (orderedRootZeroCoefficientEquiv R).toLinearEquiv
  | n + 1 =>
      let previousBaseChange :
          Module.Basis (TowerIndex n) (FactorCoefficientRing R n)
            (FactorOrderedRing R n) :=
        ((inferInstance : Algebra.IsPushout
          (CoefficientRing R n) (FactorCoefficientRing R n)
          (OrderedRootRing R n) (FactorOrderedRing R n)).out).basis
            (orderedRootBasis n)
      ((polynomialFactorBasis R n).smulTower previousBaseChange).map
        (polynomialSuccCoefficientEquiv R n).toLinearEquiv

/-- Total exponent of a nested power-basis index. -/
def towerDegree : (n : ℕ) → TowerIndex n → ℕ
  | 0, _ => 0
  | n + 1, a => a.1.1 + towerDegree n a.2

/-- The signed staircase monomial produced by the successive distinguished
roots. -/
def towerMonomial : (n : ℕ) → TowerIndex n → OrderedRootRing R n
  | 0, _ => 1
  | n + 1, a =>
      (-MvPolynomial.X (Sum.inl (0 : Fin (n + 1)))) ^ a.1.1 *
        orderedSuccShift R n (towerMonomial n a.2)

/-- The recursively composed basis has the expected signed monomial as every
basis vector. -/
@[simp]
theorem orderedRootBasis_apply : (n : ℕ) → (a : TowerIndex n) →
    orderedRootBasis R n a = towerMonomial R n a
  | 0, a => by
      rcases a with ⟨⟩
      rw [orderedRootBasis, Module.Basis.map_apply]
      simp [towerMonomial, orderedRootZeroCoefficientEquiv]
  | n + 1, a => by
      rcases a with ⟨i, a⟩
      rw [orderedRootBasis, Module.Basis.map_apply,
        Module.Basis.smulTower_apply, IsBaseChange.basis_apply,
        polynomialFactorBasis_apply, orderedRootBasis_apply n a]
      simp [towerMonomial, polynomialSuccCoefficientEquiv,
        orderedSuccShift, Algebra.smul_def]

/-- In particular, the ordered-root ring is free over the generic coefficient
ring at every finite level. -/
theorem orderedRootRing_free (n : ℕ) :
    Module.Free (CoefficientRing R n) (OrderedRootRing R n) :=
  Module.Free.of_basis (orderedRootBasis R n)

/-- The ordered-root extension is finite at every finite level. -/
theorem orderedRootRing_finite (n : ℕ) :
    Module.Finite (CoefficientRing R n) (OrderedRootRing R n) :=
  Module.Finite.of_basis (orderedRootBasis R n)

end

end LeanProofs.PolynomialFormulas.LazardInvariantOrderedRootBasis
