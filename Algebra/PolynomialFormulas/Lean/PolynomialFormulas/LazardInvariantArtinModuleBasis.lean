import PolynomialFormulas.LazardInvariantOrderedRootBasis
import PolynomialFormulas.LazardInvariantArtinBasis

/-!
# The ordered-root basis indexed by Artin exponents

This file reindexes the recursively composed power basis by the staircase
functions used for Artin monomials and removes the harmless tag on the ordered
variables.  The resulting basis has `n!` indices, each carrying Lazard's
degree bound.  Identifying the recursive coefficient map with the elementary
symmetric-polynomial map is kept as a separate theorem.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantArtinModuleBasis

open scoped Polynomial

set_option autoImplicit false

noncomputable section

variable (R : Type*) [CommRing R] [IsDomain R]

open LazardInvariantArtinBasis
open LazardInvariantOrderedRoots
open LazardInvariantOrderedRootBasis

/-- Splitting off the first staircase exponent identifies the Artin indices
at level `n + 1` with `Fin (n + 1)` times the indices at level `n`. -/
def artinIndexSuccEquiv (n : ℕ) :
    ArtinIndex (n + 1) ≃ Fin (n + 1) × ArtinIndex n :=
  (Fin.consEquiv
      (fun i : Fin (n + 1) => Fin ((n + 1) - i.1))).symm.trans
    (Equiv.prodCongr
      (finCongr (by simp))
      (Equiv.piCongrRight fun i : Fin n =>
        finCongr (by simp only [Fin.val_succ]; omega)))

@[simp]
theorem artinIndexSuccEquiv_symm_apply_zero (n : ℕ)
    (i : Fin (n + 1)) (a : ArtinIndex n) :
    (((artinIndexSuccEquiv n).symm (i, a)) 0).1 = i.1 := by
  simp [artinIndexSuccEquiv, Fin.consEquiv, Equiv.piCongrRight]

@[simp]
theorem artinIndexSuccEquiv_symm_apply_succ (n : ℕ)
    (i : Fin (n + 1)) (a : ArtinIndex n) (j : Fin n) :
    (((artinIndexSuccEquiv n).symm (i, a)) j.succ).1 = (a j).1 := by
  simp [artinIndexSuccEquiv, Fin.consEquiv, Equiv.piCongrRight,
    finCongr_apply_coe]
  rfl

/-- The nested power-basis index is exactly the Artin staircase index. -/
def towerIndexEquivArtin : (n : ℕ) → TowerIndex n ≃ ArtinIndex n
  | 0 => Equiv.ofUnique _ _
  | n + 1 =>
      (Equiv.prodCongr (Equiv.refl (Fin (n + 1)))
        (towerIndexEquivArtin n)).trans
          (artinIndexSuccEquiv n).symm

/-- Reverse coefficient order: coefficient variable `i` corresponds to the
elementary symmetric polynomial of degree `n - i`. -/
def reverseFin (n : ℕ) : Fin n ≃ Fin n where
  __ := Fin.revPerm

/-- The abstract generic coefficient ring is canonically the symmetric
subalgebra, after reversing its coefficient indices. -/
def coefficientSymmetricEquiv (n : ℕ) :
    CoefficientRing R n ≃ₐ[R]
      MvPolynomial.symmetricSubalgebra (Fin n) R :=
  (MvPolynomial.renameEquiv R (reverseFin n)).trans
    (MvPolynomial.esymmAlgEquiv (Fin n) R (by simp))

/-- The recursively constructed coefficient map after removing the tag from
the ordered variables. -/
def standardCoefficientMap (n : ℕ) :
    CoefficientRing R n →ₐ[R] MvPolynomial (Fin n) R :=
  (orderedRootPolynomialEquiv R n).toAlgHom.comp
    (orderedCoefficientMap R n)

/-- After removing the root-variable tag, the recursive coefficient map is
the inclusion of the symmetric subalgebra, composed with the explicit
coefficient-order equivalence. -/
theorem standardCoefficientMap_eq_symmetricInclusion (n : ℕ) :
    standardCoefficientMap R n =
      (MvPolynomial.symmetricSubalgebra (Fin n) R).val.comp
          (coefficientSymmetricEquiv R n).toAlgHom := by
  ext i
  have hrev : (reverseFin n i).1 + 1 = n - i.1 := by
    simp [reverseFin, Fin.val_rev]
    omega
  have hdegree : n - i.1 = n - (i.1 + 1) + 1 := by omega
  simp [standardCoefficientMap, coefficientSymmetricEquiv, reverseFin,
    orderedRootPolynomialEquiv,
    LazardInvariantOrderedRoots.orderedCoefficientMap_variable,
    MvPolynomial.rename_esymm, MvPolynomial.esymmAlgEquiv,
    MvPolynomial.esymmAlgHom, hrev, hdegree]

local instance (priority := 2000) standardRootAlgebra (n : ℕ) :
    Algebra (CoefficientRing R n) (MvPolynomial (Fin n) R) :=
  (standardCoefficientMap R n).toAlgebra

local instance (priority := 2000) standardRootModule (n : ℕ) :
    Module (CoefficientRing R n) (MvPolynomial (Fin n) R) :=
  Algebra.toModule

local instance (priority := 3000) symmetricRootAlgebra (n : ℕ) :
    Algebra (MvPolynomial.symmetricSubalgebra (Fin n) R)
      (MvPolynomial (Fin n) R) :=
  (MvPolynomial.symmetricSubalgebra (Fin n) R).val.toRingHom.toAlgebra

local instance (priority := 3000) symmetricRootModule (n : ℕ) :
    Module (MvPolynomial.symmetricSubalgebra (Fin n) R)
      (MvPolynomial (Fin n) R) :=
  Algebra.toModule

local instance orderedRootAlgebra (n : ℕ) :
    Algebra (CoefficientRing R n) (OrderedRootRing R n) :=
  (orderedCoefficientMap R n).toAlgebra

/-- Removing the variable tag respects the recursive coefficient algebra. -/
def orderedRootStandardCoefficientEquiv (n : ℕ) :
    OrderedRootRing R n ≃ₐ[CoefficientRing R n]
      MvPolynomial (Fin n) R where
  __ := orderedRootPolynomialEquiv R n
  commutes' x := by
    unfold orderedRootAlgebra standardRootAlgebra
    rfl

/-- The signed tower monomial after removing the ordered-variable tag. -/
def standardTowerMonomial (n : ℕ) (a : TowerIndex n) :
    MvPolynomial (Fin n) R :=
  orderedRootPolynomialEquiv R n (towerMonomial R n a)

/-- The recursive exponent sum agrees with the Artin degree after reindexing. -/
theorem towerDegree_eq_artinDegree : (n : ℕ) → (a : TowerIndex n) →
    towerDegree n a = artinDegree (towerIndexEquivArtin n a)
  | 0, a => by
      simp [towerDegree, artinDegree, towerIndexEquivArtin]
  | n + 1, a => by
      rcases a with ⟨i, a⟩
      simp [towerDegree, towerIndexEquivArtin,
        artinDegree, Fin.sum_univ_succ,
        towerDegree_eq_artinDegree n a]

/-- After removing the ordered-variable tags, the recursive tower basis is
the standard Artin monomial, with only the harmless sign contributed by the
successive distinguished roots `-xᵢ`. -/
theorem standardTowerMonomial_eq_monomial :
    (n : ℕ) → (a : TowerIndex n) →
      standardTowerMonomial R n a =
        MvPolynomial.monomial
          (artinExponent (towerIndexEquivArtin n a))
          ((-1 : R) ^ towerDegree n a)
  | 0, a => by
      rcases a with ⟨⟩
      have hzero :
          artinExponent (default : ArtinIndex 0) = 0 :=
        Subsingleton.elim _ _
      simp [standardTowerMonomial, towerMonomial, towerDegree,
        towerIndexEquivArtin, hzero]
  | n + 1, a => by
      rcases a with ⟨i, a⟩
      rw [standardTowerMonomial, towerMonomial, map_mul, map_pow, map_neg,
        LazardInvariantOrderedRoots.orderedRootPolynomialEquiv_orderedSuccShift]
      have hhead :
          orderedRootPolynomialEquiv R (n + 1)
              (MvPolynomial.X (Sum.inl (0 : Fin (n + 1)))) =
            MvPolynomial.X (0 : Fin (n + 1)) := by
        simp [orderedRootPolynomialEquiv, orderedVariableEquiv]
      rw [hhead]
      change (-MvPolynomial.X (0 : Fin (n + 1))) ^ i.1 *
          MvPolynomial.rename Fin.succ (standardTowerMonomial R n a) = _
      rw [standardTowerMonomial_eq_monomial n a,
        MvPolynomial.rename_monomial]
      have hexponent :
          Finsupp.single (0 : Fin (n + 1)) i.1 +
              (artinExponent (towerIndexEquivArtin n a)).mapDomain Fin.succ =
            artinExponent
              (towerIndexEquivArtin (n + 1) (i, a)) := by
        ext j
        refine Fin.cases ?_ (fun k => ?_) j
        · rw [Finsupp.add_apply, Finsupp.single_eq_same]
          rw [Finsupp.mapDomain_notin_range]
          · simp [towerIndexEquivArtin, artinExponent]
          · simp
        · rw [Finsupp.add_apply, Finsupp.single_apply,
            if_neg (Ne.symm (Fin.succ_ne_zero k)), zero_add,
            Finsupp.mapDomain_apply (Fin.succ_injective n)]
          simp [towerIndexEquivArtin, artinExponent]
      have hneg :
          (-MvPolynomial.X (0 : Fin (n + 1)) :
              MvPolynomial (Fin (n + 1)) R) ^ i.1 =
            MvPolynomial.monomial
              (Finsupp.single (0 : Fin (n + 1)) i.1)
              ((-1 : R) ^ i.1) := by
        have hc :
            (-1 : MvPolynomial (Fin (n + 1)) R) ^ i.1 =
              MvPolynomial.C ((-1 : R) ^ i.1) := by
          simpa using
            (map_pow (MvPolynomial.C : R →+* MvPolynomial (Fin (n + 1)) R)
              (-1 : R) i.1).symm
        calc
          (-MvPolynomial.X (0 : Fin (n + 1)) :
              MvPolynomial (Fin (n + 1)) R) ^ i.1 =
              (-1 : MvPolynomial (Fin (n + 1)) R) ^ i.1 *
                MvPolynomial.X (0 : Fin (n + 1)) ^ i.1 :=
            neg_pow _ _
          _ = MvPolynomial.C ((-1 : R) ^ i.1) *
                MvPolynomial.monomial
                  (Finsupp.single (0 : Fin (n + 1)) i.1) 1 := by
            rw [hc, MvPolynomial.X_pow_eq_monomial]
          _ = _ := by rw [MvPolynomial.C_mul_monomial, mul_one]
      rw [hneg, MvPolynomial.monomial_mul, hexponent,
        towerDegree, pow_add]

/-- Every recursively constructed tower monomial is homogeneous of its total
exponent degree. -/
theorem standardTowerMonomial_isHomogeneous :
    (n : ℕ) → (a : TowerIndex n) →
      MvPolynomial.IsHomogeneous (standardTowerMonomial R n a)
        (towerDegree n a)
  | 0, a => by
      rcases a with ⟨⟩
      simpa [standardTowerMonomial, towerMonomial, towerDegree,
        orderedRootPolynomialEquiv] using
          (MvPolynomial.isHomogeneous_one (σ := Fin 0) R)
  | n + 1, a => by
      rcases a with ⟨i, a⟩
      rw [standardTowerMonomial, towerMonomial, map_mul, map_pow, map_neg,
        LazardInvariantOrderedRoots.orderedRootPolynomialEquiv_orderedSuccShift]
      have hnew : MvPolynomial.IsHomogeneous
          (-MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) R) 1 :=
        (MvPolynomial.isHomogeneous_X (R := R) (0 : Fin (n + 1))).neg
      have htail :=
        (standardTowerMonomial_isHomogeneous n a).rename_isHomogeneous
          (f := Fin.succ)
      simpa [standardTowerMonomial, towerDegree,
        orderedRootPolynomialEquiv, orderedVariableEquiv] using
        (hnew.pow i.1).mul htail

/-- The full ordered-root basis, reindexed by Artin exponents in the ordinary
polynomial ring. -/
def orderedArtinBasis (n : ℕ) :
    Module.Basis (ArtinIndex n) (CoefficientRing R n)
      (MvPolynomial (Fin n) R) :=
  ((orderedRootBasis R n).reindex (towerIndexEquivArtin n)).map
    (orderedRootStandardCoefficientEquiv R n).toLinearEquiv

/-- The ambient polynomial ring basis over the actual symmetric subalgebra. -/
def symmetricArtinBasis (n : ℕ) :
    Module.Basis (ArtinIndex n)
      (MvPolynomial.symmetricSubalgebra (Fin n) R)
      (MvPolynomial (Fin n) R) :=
  (orderedArtinBasis R n).mapCoeffs
    (coefficientSymmetricEquiv R n).toRingEquiv (by
      intro c p
      simp only [Algebra.smul_def]
      have hleft :
          algebraMap (MvPolynomial.symmetricSubalgebra (Fin n) R)
              (MvPolynomial (Fin n) R)
                ((coefficientSymmetricEquiv R n).toRingEquiv c) =
            (coefficientSymmetricEquiv R n c).1 := rfl
      have hright :
          algebraMap (CoefficientRing R n) (MvPolynomial (Fin n) R) c =
            standardCoefficientMap R n c := rfl
      rw [hleft, hright, standardCoefficientMap_eq_symmetricInclusion]
      rfl)

@[simp]
theorem symmetricArtinBasis_apply (n : ℕ) (a : ArtinIndex n) :
    symmetricArtinBasis R n a =
      standardTowerMonomial R n ((towerIndexEquivArtin n).symm a) := by
  simp [symmetricArtinBasis, orderedArtinBasis, standardTowerMonomial,
    orderedRootStandardCoefficientEquiv]

/-- The symmetric Artin basis vector is literally its standard monomial,
up to the explicit nonzero sign. -/
theorem symmetricArtinBasis_apply_eq_monomial (n : ℕ) (a : ArtinIndex n) :
    symmetricArtinBasis R n a =
      MvPolynomial.monomial (artinExponent a)
        ((-1 : R) ^ artinDegree a) := by
  rw [symmetricArtinBasis_apply,
    standardTowerMonomial_eq_monomial,
    towerDegree_eq_artinDegree,
    (towerIndexEquivArtin n).apply_symm_apply]

/-- The ambient symmetric-module basis is homogeneous, with the degree
attached to its Artin index. -/
theorem symmetricArtinBasis_isHomogeneous (n : ℕ) (a : ArtinIndex n) :
    MvPolynomial.IsHomogeneous (symmetricArtinBasis R n a)
      (artinDegree a) := by
  rw [symmetricArtinBasis_apply]
  have h := standardTowerMonomial_isHomogeneous R n
    ((towerIndexEquivArtin n).symm a)
  rwa [towerDegree_eq_artinDegree,
    (towerIndexEquivArtin n).apply_symm_apply] at h

/-- Every homogeneous vector of the ambient basis satisfies Lazard's degree
bound. -/
theorem symmetricArtinBasis_degree_le (n : ℕ) (a : ArtinIndex n) :
    artinDegree a ≤ n * (n - 1) / 2 :=
  artinDegree_le a

theorem standardRootRing_free (n : ℕ) :
    Module.Free (CoefficientRing R n) (MvPolynomial (Fin n) R) :=
  Module.Free.of_basis (orderedArtinBasis R n)

theorem standardRootRing_finite (n : ℕ) :
    Module.Finite (CoefficientRing R n) (MvPolynomial (Fin n) R) :=
  Module.Finite.of_basis (orderedArtinBasis R n)

theorem symmetricRootRing_free (n : ℕ) :
    Module.Free (MvPolynomial.symmetricSubalgebra (Fin n) R)
      (MvPolynomial (Fin n) R) :=
  Module.Free.of_basis (symmetricArtinBasis R n)

theorem symmetricRootRing_finite (n : ℕ) :
    Module.Finite (MvPolynomial.symmetricSubalgebra (Fin n) R)
      (MvPolynomial (Fin n) R) :=
  Module.Finite.of_basis (symmetricArtinBasis R n)

/-- The visible rank of the ordered-root basis is `n!`. -/
theorem card_orderedArtinBasis (n : ℕ) :
    Fintype.card (ArtinIndex n) = n.factorial :=
  card_artinIndex n

/-- Every index of the ordered-root basis has Lazard's degree bound. -/
theorem orderedArtinBasis_indexDegree_le (n : ℕ) (a : ArtinIndex n) :
    artinDegree a ≤ n * (n - 1) / 2 :=
  artinDegree_le a

end

end LeanProofs.PolynomialFormulas.LazardInvariantArtinModuleBasis
