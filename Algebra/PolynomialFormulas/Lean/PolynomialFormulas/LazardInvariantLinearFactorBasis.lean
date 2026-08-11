import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing

/-!
# A linear factor of the generic monic polynomial

The coefficient map which multiplies a generic monic linear polynomial by a
generic monic polynomial of degree `n` is the one-step extension underlying
the Artin basis.  This file identifies its distinguished root and constructs
the inverse factorization in the corresponding `AdjoinRoot`.

The eventual equivalence says that this coefficient map has the power basis
`1, r, ..., r^n`.  Keeping this as a separate step makes the recursive
construction of the full `n!`-element Artin basis transparent.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantLinearFactorBasis

open scoped Polynomial TensorProduct
open Polynomial

set_option autoImplicit false

noncomputable section

variable (R : Type*) [CommRing R] [IsDomain R]
variable (n : ℕ)

/-- The ring of coefficients of the generic monic polynomial of degree
`n + 1`. -/
abbrev GenericCoefficientRing := MvPolynomial (Fin (n + 1)) R

/-- The ring carrying a generic monic linear factor and a generic monic
degree-`n` cofactor. -/
abbrev LinearFactorRing :=
  MvPolynomial (Fin 1) R ⊗[R] MvPolynomial (Fin n) R

/-- `n + 1 = 1 + n`, in the orientation used by the universal
factorization map. -/
theorem one_add_factorization : n + 1 = 1 + n := by omega

/-- The universal coefficient map induced by multiplying the two generic
factors. -/
def linearFactorCoefficientMap :
    GenericCoefficientRing R n →ₐ[R] LinearFactorRing R n :=
  MvPolynomial.universalFactorizationMap R (n + 1) 1 n
    (one_add_factorization n)

local instance linearFactorAlgebra :
    Algebra (GenericCoefficientRing R n) (LinearFactorRing R n) :=
  (linearFactorCoefficientMap R n).toAlgebra

/-- The coefficient of the generic monic linear factor. -/
def linearCoefficient : LinearFactorRing R n :=
  MvPolynomial.X (0 : Fin 1) ⊗ₜ[R] 1

/-- The root of the generic monic linear factor. -/
def distinguishedRoot : LinearFactorRing R n :=
  -linearCoefficient R n

/-- The generic monic linear factor in the target ring. -/
def genericLinearFactor : (LinearFactorRing R n)[X] :=
  (freeMonic R 1).map Algebra.TensorProduct.includeLeftRingHom

/-- The generic monic degree-`n` cofactor in the target ring. -/
def genericCofactor : (LinearFactorRing R n)[X] :=
  (freeMonic R n).map Algebra.TensorProduct.includeRight.toRingHom

theorem genericLinearFactor_eq :
    genericLinearFactor R n = X - C (distinguishedRoot R n) := by
  simp [genericLinearFactor, freeMonic, distinguishedRoot, linearCoefficient]

theorem genericPolynomial_factorization :
    (freeMonic R (n + 1)).map (linearFactorCoefficientMap R n).toRingHom =
      genericLinearFactor R n * genericCofactor R n := by
  exact MvPolynomial.universalFactorizationMap_freeMonic R (n + 1) 1 n
    (one_add_factorization n)

theorem distinguishedRoot_isRoot :
    (freeMonic R (n + 1)).eval₂ (linearFactorCoefficientMap R n).toRingHom
      (distinguishedRoot R n) = 0 := by
  rw [← eval_map, genericPolynomial_factorization, eval_mul,
    genericLinearFactor_eq]
  simp

/-- The adjoin-root presentation of the generic ordered root. -/
abbrev GenericRootRing := AdjoinRoot (freeMonic R (n + 1))

local instance genericRootRing_nontrivial : Nontrivial (GenericRootRing R n) :=
  AdjoinRoot.nontrivial (f := freeMonic R (n + 1)) <| by
    rw [degree_freeMonic]
    exact_mod_cast Nat.succ_ne_zero n

/-- The generic polynomial after adjoining its distinguished root. -/
def mappedGenericPolynomial : (GenericRootRing R n)[X] :=
  (freeMonic R (n + 1)).map (AdjoinRoot.of (freeMonic R (n + 1)))

/-- Synthetic division by the distinguished linear factor. -/
def quotientFactor : (GenericRootRing R n)[X] :=
  mappedGenericPolynomial R n /ₘ
    (X - C (AdjoinRoot.root (freeMonic R (n + 1))))

theorem linear_mul_quotientFactor :
    (X - C (AdjoinRoot.root (freeMonic R (n + 1)))) * quotientFactor R n =
      mappedGenericPolynomial R n := by
  exact mul_divByMonic_eq_iff_isRoot.mpr
    (AdjoinRoot.isRoot_root (freeMonic R (n + 1)))

theorem quotientFactor_monic : (quotientFactor R n).Monic := by
  apply (monic_X_sub_C (AdjoinRoot.root (freeMonic R (n + 1)))).of_mul_monic_left
  rw [linear_mul_quotientFactor]
  exact (monic_freeMonic R (n + 1)).map _

theorem quotientFactor_natDegree : (quotientFactor R n).natDegree = n := by
  rw [quotientFactor,
    natDegree_divByMonic _ (monic_X_sub_C
      (AdjoinRoot.root (freeMonic R (n + 1)))),
    mappedGenericPolynomial,
    (monic_freeMonic R (n + 1)).natDegree_map,
    natDegree_freeMonic, natDegree_X_sub_C]
  omega

/-- The linear factor as a fixed-degree monic polynomial. -/
def rootLinearFactor : MonicDegreeEq (GenericRootRing R n) 1 :=
  MonicDegreeEq.mk
    (X - C (AdjoinRoot.root (freeMonic R (n + 1))))
    (monic_X_sub_C _) (natDegree_X_sub_C _)

/-- The quotient factor as a fixed-degree monic polynomial. -/
def rootQuotientFactor : MonicDegreeEq (GenericRootRing R n) n :=
  MonicDegreeEq.mk (quotientFactor R n) (quotientFactor_monic R n)
    (quotientFactor_natDegree R n)

theorem rootFactorization :
    (rootLinearFactor R n).1 * (rootQuotientFactor R n).1 =
      ((MonicDegreeEq.freeMonic R (n + 1)).map
        (AdjoinRoot.of (freeMonic R (n + 1)))).1 := by
  exact linear_mul_quotientFactor R n

/-- The ordered factorization in the generic root ring. -/
def rootFactorizationData :
    {q : MonicDegreeEq (GenericRootRing R n) 1 ×
        MonicDegreeEq (GenericRootRing R n) n //
      q.1.1 * q.2.1 =
        ((MonicDegreeEq.freeMonic R (n + 1)).map
          (AdjoinRoot.of (freeMonic R (n + 1)))).1} :=
  ⟨(rootLinearFactor R n, rootQuotientFactor R n), rootFactorization R n⟩

/-- The universal factorization map associated to the ordered factorization
inside the generic root ring. -/
def factorizationToRootOverR :
    LinearFactorRing R n →ₐ[R] GenericRootRing R n :=
  ((MvPolynomial.universalFactorizationMapLiftEquiv R (GenericRootRing R n)
    (n + 1) 1 n (one_add_factorization n)
    ((MonicDegreeEq.freeMonic R (n + 1)).map
      (AdjoinRoot.of (freeMonic R (n + 1))))).symm
      (rootFactorizationData R n)).1

theorem mapEquivMonic_symm_mapped_freeMonic :
    (MvPolynomial.mapEquivMonic R (GenericRootRing R n) (n + 1)).symm
        ((MonicDegreeEq.freeMonic R (n + 1)).map
          (AdjoinRoot.of (freeMonic R (n + 1)))) =
      AdjoinRoot.ofAlgHom R (freeMonic R (n + 1)) := by
  let g := AdjoinRoot.ofAlgHom R (freeMonic R (n + 1))
  have hid :
      (MvPolynomial.mapEquivMonic R (GenericCoefficientRing R n) (n + 1)).symm
          (MonicDegreeEq.freeMonic R (n + 1)) =
        AlgHom.id R (GenericCoefficientRing R n) := by
    apply (MvPolynomial.mapEquivMonic R (GenericCoefficientRing R n) (n + 1)).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    change freeMonic R (n + 1) =
      (freeMonic R (n + 1)).map (RingHom.id (GenericCoefficientRing R n))
    simp
  calc
    _ = g.comp
        ((MvPolynomial.mapEquivMonic R (GenericCoefficientRing R n) (n + 1)).symm
          (MonicDegreeEq.freeMonic R (n + 1))) := by
          simpa [g] using
            (MvPolynomial.mapEquivMonic_symm_map
              (n := n + 1) (p := MonicDegreeEq.freeMonic R (n + 1)) (g := g))
    _ = g := by rw [hid, AlgHom.comp_id]

theorem factorizationToRootOverR_comp :
    (factorizationToRootOverR R n).comp (linearFactorCoefficientMap R n) =
      AdjoinRoot.ofAlgHom R (freeMonic R (n + 1)) := by
  change
    (((MvPolynomial.universalFactorizationMapLiftEquiv R (GenericRootRing R n)
      (n + 1) 1 n (one_add_factorization n)
      ((MonicDegreeEq.freeMonic R (n + 1)).map
        (AdjoinRoot.of (freeMonic R (n + 1))))).symm
        (rootFactorizationData R n)).1).comp
          (linearFactorCoefficientMap R n) = _
  exact (((MvPolynomial.universalFactorizationMapLiftEquiv R (GenericRootRing R n)
    (n + 1) 1 n (one_add_factorization n)
    ((MonicDegreeEq.freeMonic R (n + 1)).map
      (AdjoinRoot.of (freeMonic R (n + 1))))).symm
        (rootFactorizationData R n)).2).trans
          (mapEquivMonic_symm_mapped_freeMonic R n)

/-- The inverse factorization map, now regarded as an algebra homomorphism
over the generic coefficient ring. -/
def factorizationToRoot :
    LinearFactorRing R n →ₐ[GenericCoefficientRing R n] GenericRootRing R n where
  __ := (factorizationToRootOverR R n).toRingHom
  commutes' x := by
    have h := DFunLike.congr_fun (factorizationToRootOverR_comp R n) x
    exact h

@[simp]
theorem factorizationToRoot_linearCoefficient :
    factorizationToRoot R n (linearCoefficient R n) =
      -AdjoinRoot.root (freeMonic R (n + 1)) := by
  change (factorizationToRootOverR R n) (linearCoefficient R n) = _
  let E := MvPolynomial.universalFactorizationMapLiftEquiv R (GenericRootRing R n)
    (n + 1) 1 n (one_add_factorization n)
    ((MonicDegreeEq.freeMonic R (n + 1)).map
      (AdjoinRoot.of (freeMonic R (n + 1))))
  have hpair := E.apply_symm_apply (rootFactorizationData R n)
  have hleft := congrArg (fun q => q.1.1.1) hpair
  change
    ((MonicDegreeEq.freeMonic R 1).map
      ((factorizationToRootOverR R n).comp
        Algebra.TensorProduct.includeLeft)).1 =
      (rootLinearFactor R n).1 at hleft
  have hc := congrArg (fun p => p.coeff 0) hleft
  simpa [linearCoefficient, MonicDegreeEq.freeMonic, coeff_freeMonic,
    rootLinearFactor] using hc

@[simp]
theorem factorizationToRoot_distinguishedRoot :
    factorizationToRoot R n (distinguishedRoot R n) =
      AdjoinRoot.root (freeMonic R (n + 1)) := by
  simp [distinguishedRoot]

@[simp]
theorem factorizationToRoot_rightVariable (i : Fin n) :
    factorizationToRoot R n (1 ⊗ₜ[R] MvPolynomial.X i) =
      (quotientFactor R n).coeff i := by
  change (factorizationToRootOverR R n) (1 ⊗ₜ[R] MvPolynomial.X i) = _
  let E := MvPolynomial.universalFactorizationMapLiftEquiv R (GenericRootRing R n)
    (n + 1) 1 n (one_add_factorization n)
    ((MonicDegreeEq.freeMonic R (n + 1)).map
      (AdjoinRoot.of (freeMonic R (n + 1))))
  have hpair := E.apply_symm_apply (rootFactorizationData R n)
  have hright := congrArg (fun q => q.1.2.1) hpair
  change
    ((MonicDegreeEq.freeMonic R n).map
      ((factorizationToRootOverR R n).comp
        Algebra.TensorProduct.includeRight)).1 =
      (rootQuotientFactor R n).1 at hright
  have hc := congrArg (fun p => p.coeff i) hright
  simpa [MonicDegreeEq.freeMonic, coeff_freeMonic,
    rootQuotientFactor] using hc

/-- Evaluation at the distinguished root gives the forward map from the
adjoin-root presentation to the factorization presentation. -/
def rootToFactorization :
    GenericRootRing R n →ₐ[GenericCoefficientRing R n] LinearFactorRing R n :=
  AdjoinRoot.liftAlgHom (freeMonic R (n + 1))
    (Algebra.ofId (GenericCoefficientRing R n) (LinearFactorRing R n))
    (distinguishedRoot R n) <| by
      exact distinguishedRoot_isRoot R n

@[simp]
theorem rootToFactorization_root :
    rootToFactorization R n (AdjoinRoot.root (freeMonic R (n + 1))) =
      distinguishedRoot R n := by
  simp [rootToFactorization]

theorem map_mappedGenericPolynomial :
    (mappedGenericPolynomial R n).map (rootToFactorization R n).toRingHom =
      (freeMonic R (n + 1)).map (linearFactorCoefficientMap R n).toRingHom := by
  rw [mappedGenericPolynomial, Polynomial.map_map]
  have hcomp :
      (rootToFactorization R n).toRingHom.comp
          (AdjoinRoot.of (freeMonic R (n + 1))) =
        (linearFactorCoefficientMap R n).toRingHom := by
    apply RingHom.ext
    intro x
    exact (rootToFactorization R n).commutes x
  rw [hcomp]

theorem map_quotientFactor :
    (quotientFactor R n).map (rootToFactorization R n).toRingHom =
      genericCofactor R n := by
  rw [quotientFactor,
    Polynomial.map_divByMonic _ (monic_X_sub_C
      (AdjoinRoot.root (freeMonic R (n + 1)))),
    map_mappedGenericPolynomial, genericPolynomial_factorization]
  have hlinear :
      (X - C (AdjoinRoot.root (freeMonic R (n + 1)))).map
          (rootToFactorization R n).toRingHom =
        genericLinearFactor R n := by
    simp [genericLinearFactor_eq]
  rw [hlinear]
  exact mul_divByMonic_cancel_left (genericCofactor R n)
    ((monic_freeMonic R 1).map _)

@[simp]
theorem rootToFactorization_quotientFactor_coeff (i : Fin n) :
    rootToFactorization R n ((quotientFactor R n).coeff i) =
      1 ⊗ₜ[R] MvPolynomial.X i := by
  have hc := congrArg (fun p => p.coeff i) (map_quotientFactor R n)
  simpa [genericCofactor, coeff_freeMonic] using hc

theorem factorizationToRoot_comp_rootToFactorization :
    (factorizationToRoot R n).comp (rootToFactorization R n) =
      AlgHom.id (GenericCoefficientRing R n) (GenericRootRing R n) := by
  apply AdjoinRoot.algHom_ext
  simp

theorem rootToFactorization_comp_factorizationToRoot :
    (rootToFactorization R n).comp (factorizationToRoot R n) =
      AlgHom.id (GenericCoefficientRing R n) (LinearFactorRing R n) := by
  apply AlgHom.restrictScalars_injective R
  apply Algebra.TensorProduct.ext
  · ext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    change
      rootToFactorization R n
          (factorizationToRoot R n (linearCoefficient R n)) =
        linearCoefficient R n
    rw [factorizationToRoot_linearCoefficient, map_neg,
      rootToFactorization_root]
    simp [distinguishedRoot]
  · ext i
    simp

/-- The generic linear-factor coefficient ring is precisely the adjoin-root
ring of the generic monic polynomial. -/
def linearFactorAlgEquiv :
    GenericRootRing R n ≃ₐ[GenericCoefficientRing R n] LinearFactorRing R n :=
  AlgEquiv.ofAlgHom (rootToFactorization R n) (factorizationToRoot R n)
    (rootToFactorization_comp_factorizationToRoot R n)
    (factorizationToRoot_comp_rootToFactorization R n)

@[simp]
theorem linearFactorAlgEquiv_root :
    linearFactorAlgEquiv R n (AdjoinRoot.root (freeMonic R (n + 1))) =
      distinguishedRoot R n := by
  exact rootToFactorization_root R n

/-- The rank-`n + 1` power basis on the generic linear-factor ring. -/
def linearFactorPowerBasis :
    PowerBasis (GenericCoefficientRing R n) (LinearFactorRing R n) :=
  (AdjoinRoot.powerBasis' (monic_freeMonic R (n + 1))).map
    (linearFactorAlgEquiv R n)

@[simp]
theorem linearFactorPowerBasis_gen :
    (linearFactorPowerBasis R n).gen = distinguishedRoot R n := by
  simp [linearFactorPowerBasis, linearFactorAlgEquiv_root]

@[simp]
theorem linearFactorPowerBasis_dim :
    (linearFactorPowerBasis R n).dim = n + 1 := by
  simp [linearFactorPowerBasis, AdjoinRoot.powerBasis', natDegree_freeMonic]

/-- The same power basis, reindexed by the visible degree `n + 1`. -/
def linearFactorBasis :
    Module.Basis (Fin (n + 1)) (GenericCoefficientRing R n) (LinearFactorRing R n) :=
  (((AdjoinRoot.powerBasis' (monic_freeMonic R (n + 1))).basis.map
    (linearFactorAlgEquiv R n).toLinearEquiv).reindex
      (finCongr (natDegree_freeMonic R (n + 1))))

@[simp]
theorem linearFactorBasis_apply (i : Fin (n + 1)) :
    linearFactorBasis R n i = (distinguishedRoot R n) ^ (i : ℕ) := by
  rw [linearFactorBasis, Module.Basis.reindex_apply, Module.Basis.map_apply,
    PowerBasis.coe_basis]
  simp [linearFactorAlgEquiv_root]

/-- In particular the one-step generic factorization extension is honestly
finite free; no projectivity or freeness hypothesis is used. -/
theorem linearFactorRing_free :
    Module.Free (GenericCoefficientRing R n) (LinearFactorRing R n) :=
  Module.Free.of_basis (linearFactorBasis R n)

theorem linearFactorRing_finite :
    Module.Finite (GenericCoefficientRing R n) (LinearFactorRing R n) :=
  Module.Finite.of_basis (linearFactorBasis R n)

end

end LeanProofs.PolynomialFormulas.LazardInvariantLinearFactorBasis
