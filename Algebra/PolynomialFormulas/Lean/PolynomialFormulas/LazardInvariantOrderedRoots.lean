import PolynomialFormulas.LazardInvariantLinearFactorBasis
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# The ordered-root tower behind the Artin basis

This file iterates the one-linear-factor power basis.  At level `n` the
coefficient ring is a polynomial ring in the coefficients of a generic monic
degree-`n` polynomial, while the ordered-root ring is a polynomial ring in
`n` independent linear-factor coefficients.  The coefficient map is obtained
by multiplying the `n` generic linear factors.

The construction is kept over an arbitrary integral domain.  In particular,
no freeness or projectivity hypothesis is used.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantOrderedRoots

open scoped Polynomial TensorProduct
open Polynomial

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

variable (R : Type*) [CommRing R] [IsDomain R]

/-- The abstract coefficient ring for a generic monic degree-`n` polynomial. -/
abbrev CoefficientRing (n : ℕ) := MvPolynomial (Fin n) R

/-- A tagged copy of `Fin n`.  Keeping the ordered-root variables definitionally
distinct from the generic coefficient variables prevents spurious self-algebra
instances while constructing the scalar tower. -/
abbrev OrderedVariable (n : ℕ) := Fin n ⊕ PEmpty.{1}

/-- The polynomial ring in `n` ordered linear-factor coefficients. -/
abbrev OrderedRootRing (n : ℕ) := MvPolynomial (OrderedVariable n) R

/-- Add one ordered variable at the front of the tagged finite family. -/
def orderedSuccVariableEquiv (n : ℕ) :
    Fin 1 ⊕ OrderedVariable n ≃ OrderedVariable (n + 1) :=
  (Equiv.sumAssoc (Fin 1) (Fin n) PEmpty).symm.trans
    (Equiv.sumCongr
      (finSumFinEquiv.trans (finCongr (Nat.one_add n)))
      (Equiv.refl PEmpty))

/-- Remove the empty tag from the ordered variable family. -/
def orderedVariableEquiv (n : ℕ) : OrderedVariable n ≃ Fin n :=
  Equiv.sumEmpty (Fin n) PEmpty

/-- The ordered-root polynomial ring is an ordinary polynomial ring in `n`
variables, with only a tag separating its scalar-tower role. -/
def orderedRootPolynomialEquiv (n : ℕ) :
    OrderedRootRing R n ≃ₐ[R] MvPolynomial (Fin n) R :=
  MvPolynomial.renameEquiv R (orderedVariableEquiv n)

/-- The same one-factor ring, written as a polynomial ring over the generic
cofactor coefficient ring. -/
abbrev FactorCoefficientRing (n : ℕ) :=
  MvPolynomial (Fin 1) (CoefficientRing R n)

/-- One new ordered factor over the preceding ordered-root ring. -/
abbrev FactorOrderedRing (n : ℕ) :=
  MvPolynomial (Fin 1) (OrderedRootRing R n)

local instance linearFactorRightAlgebra (n : ℕ) :
    Algebra (CoefficientRing R n)
      (LazardInvariantLinearFactorBasis.LinearFactorRing R n) :=
  Algebra.TensorProduct.rightAlgebra

/-- Reassociate the tensor presentation of a generic linear factor as a
one-variable polynomial ring over the generic cofactor coefficients. -/
def linearFactorPolynomialEquiv (n : ℕ) :
    LazardInvariantLinearFactorBasis.LinearFactorRing R n ≃ₐ[CoefficientRing R n]
      FactorCoefficientRing R n :=
  (Algebra.TensorProduct.commRight R (CoefficientRing R n)
      (MvPolynomial (Fin 1) R)).symm.trans
    (MvPolynomial.algebraTensorAlgEquiv (σ := Fin 1) R
      (CoefficientRing R n))

/-- Flatten a one-variable polynomial ring over `n` ordered variables into
the ordered-root ring on `n + 1` variables. -/
def polynomialSuccEquiv (n : ℕ) :
    FactorOrderedRing R n ≃ₐ[R] OrderedRootRing R (n + 1) :=
  (MvPolynomial.sumAlgEquiv R (Fin 1) (OrderedVariable n)).symm.trans
    (MvPolynomial.renameEquiv R (orderedSuccVariableEquiv n))

@[simp]
theorem polynomialSuccEquiv_variable (n : ℕ) :
    polynomialSuccEquiv R n (MvPolynomial.X (0 : Fin 1)) =
      MvPolynomial.X (Sum.inl (0 : Fin (n + 1))) := by
  simp [polynomialSuccEquiv, orderedSuccVariableEquiv]
  apply Fin.ext
  rfl

@[simp]
theorem polynomialSuccEquiv_coefficientVariable (n : ℕ) (i : Fin n) :
    polynomialSuccEquiv R n
        (MvPolynomial.C (MvPolynomial.X (Sum.inl i : OrderedVariable n))) =
      MvPolynomial.X (Sum.inl i.succ : OrderedVariable (n + 1)) := by
  simp [polynomialSuccEquiv, orderedSuccVariableEquiv]

/-- The one-step coefficient map in the polynomial-over-coefficients
presentation. -/
def polynomialFactorCoefficientMap (n : ℕ) :
    CoefficientRing R (n + 1) →ₐ[R] FactorCoefficientRing R n :=
  ((linearFactorPolynomialEquiv R n).toAlgHom.restrictScalars R).comp
    (LazardInvariantLinearFactorBasis.linearFactorCoefficientMap R n)

@[simp]
theorem linearFactorPolynomialEquiv_distinguishedRoot (n : ℕ) :
    linearFactorPolynomialEquiv R n
        (LazardInvariantLinearFactorBasis.distinguishedRoot R n) =
      -MvPolynomial.X (0 : Fin 1) := by
  simp [linearFactorPolynomialEquiv,
    LazardInvariantLinearFactorBasis.distinguishedRoot,
    LazardInvariantLinearFactorBasis.linearCoefficient]

/-- In polynomial-over-coefficients form, the universal one-factor map says
that the generic degree-`n + 1` polynomial is the new generic linear factor
times the generic degree-`n` cofactor. -/
theorem polynomialFactorCoefficientMap_freeMonic (n : ℕ) :
    (freeMonic R (n + 1)).map (polynomialFactorCoefficientMap R n).toRingHom =
      (Polynomial.X + Polynomial.C (MvPolynomial.X (0 : Fin 1))) *
        (freeMonic R n).map (MvPolynomial.C :
          CoefficientRing R n →+* FactorCoefficientRing R n) := by
  have hlinear :
      (LazardInvariantLinearFactorBasis.genericLinearFactor R n).map
          (linearFactorPolynomialEquiv R n).toRingEquiv.toRingHom =
        Polynomial.X + Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
    rw [LazardInvariantLinearFactorBasis.genericLinearFactor_eq]
    simp [linearFactorPolynomialEquiv_distinguishedRoot, sub_eq_add_neg]
  have hcofactor :
      (LazardInvariantLinearFactorBasis.genericCofactor R n).map
          (linearFactorPolynomialEquiv R n).toRingEquiv.toRingHom =
        (freeMonic R n).map (MvPolynomial.C :
          CoefficientRing R n →+* FactorCoefficientRing R n) := by
    have hright :
        (linearFactorPolynomialEquiv R n).toRingEquiv.toRingHom.comp
            Algebra.TensorProduct.includeRight.toRingHom =
          (MvPolynomial.C :
            CoefficientRing R n →+* FactorCoefficientRing R n) := by
      apply DFunLike.ext _ _
      intro a
      simp [linearFactorPolynomialEquiv]
      rw [Algebra.smul_def]
      simp
    simpa only [LazardInvariantLinearFactorBasis.genericCofactor,
      Polynomial.map_map, hright]
  have h := congrArg
    (Polynomial.map (linearFactorPolynomialEquiv R n).toRingEquiv.toRingHom)
    (LazardInvariantLinearFactorBasis.genericPolynomial_factorization R n)
  rw [Polynomial.map_mul, hlinear, hcofactor] at h
  have hcomp :
      (linearFactorPolynomialEquiv R n).toRingEquiv.toRingHom.comp
          (LazardInvariantLinearFactorBasis.linearFactorCoefficientMap R n).toRingHom =
        (((linearFactorPolynomialEquiv R n).toAlgHom.restrictScalars R).comp
          (LazardInvariantLinearFactorBasis.linearFactorCoefficientMap R n)).toRingHom := by
    apply DFunLike.ext _ _
    intro a
    rfl
  rw [Polynomial.map_map] at h
  rw [hcomp] at h
  simpa only [polynomialFactorCoefficientMap] using h

/-- Extend a complete factorization of the generic degree-`n` polynomial by
one new ordered linear factor. -/
def orderedCoefficientStep (n : ℕ)
    (f : CoefficientRing R n →ₐ[R] OrderedRootRing R n) :
    CoefficientRing R (n + 1) →ₐ[R] OrderedRootRing R (n + 1) :=
  (polynomialSuccEquiv R n).toAlgHom.comp
    ((MvPolynomial.mapAlgHom f).comp (polynomialFactorCoefficientMap R n))

/-- The universal coefficient map obtained by multiplying all ordered generic
linear factors.  At level zero the tagged empty variable family is identified
with the ordinary empty family explicitly. -/
def orderedCoefficientMap : (n : ℕ) →
    CoefficientRing R n →ₐ[R] OrderedRootRing R n
  | 0 => (orderedRootPolynomialEquiv R 0).symm.toAlgHom
  | n + 1 => orderedCoefficientStep R n (orderedCoefficientMap n)

/-- The product of the ordered generic linear factors, written in the same
recursive polynomial tower as `orderedCoefficientMap`. -/
def recursiveFactorProduct : (n : ℕ) → Polynomial (OrderedRootRing R n)
  | 0 => 1
  | n + 1 =>
      (Polynomial.X + Polynomial.C
          (MvPolynomial.X (Sum.inl (0 : Fin (n + 1))))) *
        ((recursiveFactorProduct n).map
          (MvPolynomial.C : OrderedRootRing R n →+* FactorOrderedRing R n)).map
            (polynomialSuccEquiv R n).toRingEquiv.toRingHom

/-- Shift an ordered-root polynomial into the tail variables at the next
level. -/
def orderedSuccShift (n : ℕ) :
    OrderedRootRing R n →ₐ[R] OrderedRootRing R (n + 1) :=
  (polynomialSuccEquiv R n).toAlgHom.comp
    (IsScalarTower.toAlgHom R (OrderedRootRing R n)
      (FactorOrderedRing R n))

@[simp]
theorem orderedSuccShift_variable (n : ℕ) (i : Fin n) :
    orderedSuccShift R n
        (MvPolynomial.X (Sum.inl i : OrderedVariable n)) =
      MvPolynomial.X (Sum.inl i.succ : OrderedVariable (n + 1)) := by
  exact polynomialSuccEquiv_coefficientVariable R n i

/-- Removing the variable tag turns the recursive tail embedding into the
ordinary `Fin.succ` renaming. -/
theorem orderedRootPolynomialEquiv_orderedSuccShift (n : ℕ)
    (p : OrderedRootRing R n) :
    orderedRootPolynomialEquiv R (n + 1) (orderedSuccShift R n p) =
      MvPolynomial.rename Fin.succ (orderedRootPolynomialEquiv R n p) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp [orderedSuccShift, orderedRootPolynomialEquiv]
  | add p q hp hq =>
      simp [map_add, hp, hq]
  | mul_X p i hp =>
      rcases i with i | i
      · simp only [map_mul, hp, orderedSuccShift_variable]
        simp [orderedRootPolynomialEquiv, orderedVariableEquiv]
      · exact PEmpty.elim i

/-- The product of all ordered generic linear factors. -/
def orderedFactorProduct (n : ℕ) : Polynomial (OrderedRootRing R n) :=
  ∏ i : OrderedVariable n,
    (Polynomial.X + Polynomial.C (MvPolynomial.X i))

/-- Splitting off the first variable gives the recursive equation for the
full product of ordered factors. -/
theorem orderedFactorProduct_succ (n : ℕ) :
    orderedFactorProduct R (n + 1) =
      (Polynomial.X + Polynomial.C
          (MvPolynomial.X (Sum.inl (0 : Fin (n + 1))))) *
        (orderedFactorProduct R n).map (orderedSuccShift R n).toRingHom := by
  classical
  let F : OrderedVariable (n + 1) → Polynomial (OrderedRootRing R (n + 1)) :=
    fun i => Polynomial.X + Polynomial.C (MvPolynomial.X i)
  calc
    orderedFactorProduct R (n + 1) = ∏ i, F i := rfl
    _ = ∏ i : Fin 1 ⊕ OrderedVariable n,
        F (orderedSuccVariableEquiv n i) := by
      symm
      exact Fintype.prod_equiv (orderedSuccVariableEquiv n) _ _ fun _ => rfl
    _ = F (orderedSuccVariableEquiv n (Sum.inl 0)) *
        ∏ i : OrderedVariable n,
          F (orderedSuccVariableEquiv n (Sum.inr i)) := by
      rw [Fintype.prod_sum_type]
      simp
    _ = _ := by
      have hhead :
          F (orderedSuccVariableEquiv n (Sum.inl 0)) =
            Polynomial.X + Polynomial.C
              (MvPolynomial.X (Sum.inl (0 : Fin (n + 1)))) := by
        simp [F, orderedSuccVariableEquiv]
        apply Fin.ext
        rfl
      have htail :
          (∏ i : OrderedVariable n,
              F (orderedSuccVariableEquiv n (Sum.inr i))) =
            (orderedFactorProduct R n).map
              (orderedSuccShift R n).toRingHom := by
        simp [F, orderedFactorProduct, OrderedVariable,
          orderedSuccVariableEquiv, orderedSuccShift_variable,
          Polynomial.map_prod]
      rw [hhead, htail]

/-- Mapping the generic monic polynomial by the recursive coefficient map
really produces the recursively accumulated product of linear factors. -/
theorem map_freeMonic_orderedCoefficientMap (n : ℕ) :
    (freeMonic R n).map (orderedCoefficientMap R n).toRingHom =
      recursiveFactorProduct R n := by
  induction n with
  | zero =>
      simp [orderedCoefficientMap, recursiveFactorProduct, freeMonic]
  | succ n ih =>
      calc
        (freeMonic R (n + 1)).map
            (orderedCoefficientMap R (n + 1)).toRingHom =
          ((((freeMonic R (n + 1)).map
              (polynomialFactorCoefficientMap R n).toRingHom).map
                (MvPolynomial.map
                  (orderedCoefficientMap R n).toRingHom)).map
                    (polynomialSuccEquiv R n).toRingEquiv.toRingHom) := by
              simp only [orderedCoefficientMap, orderedCoefficientStep,
                Polynomial.map_map]
              congr 1
        _ = recursiveFactorProduct R (n + 1) := by
          have htail :
              (freeMonic R n).map
                  ((polynomialSuccEquiv R n).toRingEquiv.toRingHom.comp
                    ((MvPolynomial.map
                      (orderedCoefficientMap R n).toRingHom).comp
                        (MvPolynomial.C : CoefficientRing R n →+*
                          FactorCoefficientRing R n))) =
                (recursiveFactorProduct R n).map
                  ((polynomialSuccEquiv R n).toRingEquiv.toRingHom.comp
                    (MvPolynomial.C : OrderedRootRing R n →+*
                      FactorOrderedRing R n)) := by
            have ht := congrArg
              (Polynomial.map
                ((polynomialSuccEquiv R n).toRingEquiv.toRingHom.comp
                  (MvPolynomial.C : OrderedRootRing R n →+*
                    FactorOrderedRing R n))) ih
            rw [Polynomial.map_map] at ht
            have hmaps :
                (polynomialSuccEquiv R n).toRingEquiv.toRingHom.comp
                    ((MvPolynomial.map
                      (orderedCoefficientMap R n).toRingHom).comp
                        (MvPolynomial.C : CoefficientRing R n →+*
                          FactorCoefficientRing R n)) =
                  (((polynomialSuccEquiv R n).toRingEquiv.toRingHom.comp
                    (MvPolynomial.C : OrderedRootRing R n →+*
                      FactorOrderedRing R n)).comp
                        (orderedCoefficientMap R n).toRingHom) := by
              apply DFunLike.ext _ _
              intro a
              simp
            rw [hmaps]
            exact ht
          rw [polynomialFactorCoefficientMap_freeMonic]
          simp only [Polynomial.map_mul, Polynomial.map_map,
            recursiveFactorProduct]
          rw [htail]
          congr 1
          simp [polynomialSuccEquiv_variable]

/-- The recursive product contains every ordered factor exactly once. -/
theorem recursiveFactorProduct_eq_orderedFactorProduct (n : ℕ) :
    recursiveFactorProduct R n = orderedFactorProduct R n := by
  induction n with
  | zero =>
      simp [recursiveFactorProduct, orderedFactorProduct, OrderedVariable]
  | succ n ih =>
      have htail :
          ((orderedFactorProduct R n).map
              (MvPolynomial.C : OrderedRootRing R n →+*
                FactorOrderedRing R n)).map
                (polynomialSuccEquiv R n).toRingEquiv.toRingHom =
            (orderedFactorProduct R n).map
              (orderedSuccShift R n).toRingHom := by
        rw [Polynomial.map_map]
        congr 1
      rw [recursiveFactorProduct, orderedFactorProduct_succ, ih, htail]

/-- Consequently, the recursive coefficient map sends the generic monic
polynomial to the literal product of all its ordered generic factors. -/
theorem map_freeMonic_orderedCoefficientMap_eq_product (n : ℕ) :
    (freeMonic R n).map (orderedCoefficientMap R n).toRingHom =
      orderedFactorProduct R n := by
  rw [map_freeMonic_orderedCoefficientMap,
    recursiveFactorProduct_eq_orderedFactorProduct]

/-- The same intended coefficient map written directly with Vieta's formula:
the coefficient of `X^i` in the product of all ordered linear factors is the
elementary symmetric polynomial of degree `n - i`.  The equality below is the
bridge from the recursive power-basis construction to Mathlib's
`esymmAlgEquiv`. -/
def vietaCoefficientMap (n : ℕ) :
    CoefficientRing R n →ₐ[R] OrderedRootRing R n :=
  MvPolynomial.aeval fun i : Fin n =>
    MvPolynomial.esymm (OrderedVariable n) R (n - i.1)

/-- Vieta's coefficient formula for the recursively constructed map. -/
theorem orderedCoefficientMap_variable (n : ℕ) (i : Fin n) :
    orderedCoefficientMap R n (MvPolynomial.X i) =
      MvPolynomial.esymm (OrderedVariable n) R (n - i.1) := by
  have hcoeff := congrArg (fun p => p.coeff i.1)
    (map_freeMonic_orderedCoefficientMap_eq_product R n)
  have hmap :
      orderedCoefficientMap R n (MvPolynomial.X i) =
        (orderedFactorProduct R n).coeff i.1 := by
    simpa [Polynomial.coeff_map, coeff_freeMonic, i.2] using hcoeff
  rw [hmap]
  have hi : i.1 ≤ Fintype.card (OrderedVariable n) := by
    simpa [OrderedVariable] using Nat.le_of_lt i.2
  simpa [orderedFactorProduct, OrderedVariable] using
    (MvPolynomial.prod_X_add_C_coeff R (OrderedVariable n) i.1 hi)

/-- The recursive universal-factorization map is exactly the direct Vieta
map.  Thus no coefficient identity is supplied as an external certificate. -/
theorem orderedCoefficientMap_eq_vietaCoefficientMap (n : ℕ) :
    orderedCoefficientMap R n = vietaCoefficientMap R n := by
  ext i
  simp [vietaCoefficientMap, orderedCoefficientMap_variable]

@[simp]
theorem orderedCoefficientMap_zero :
    orderedCoefficientMap R 0 =
      (orderedRootPolynomialEquiv R 0).symm.toAlgHom :=
  rfl

theorem orderedCoefficientMap_succ (n : ℕ) :
    orderedCoefficientMap R (n + 1) =
      orderedCoefficientStep R n (orderedCoefficientMap R n) :=
  rfl

end

end LeanProofs.PolynomialFormulas.LazardInvariantOrderedRoots
