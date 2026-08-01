import PolynomialFormulas.SexticSeparatingInvariants

/-!
# Universal collision-safe evaluated resolvents

For every natural evaluation pair, the degree-15 and degree-10 descriptor
resolvents have symmetric coefficients in the six root variables.  The
fundamental theorem of symmetric polynomials therefore expresses those
coefficients uniformly in the six elementary symmetric functions.
-/

open scoped BigOperators
open Equiv MvPolynomial Polynomial

namespace LeanProofs.PolynomialFormulas.SexticEvaluatedResolvents

open Fin6BlockSystems
open SexticSeparatingInvariants

abbrev RootRing := MvPolynomial (Fin 6) ℤ

noncomputable def rootVariables : Fin 6 → RootRing := fun i ↦ MvPolynomial.X i

noncomputable def pairUniversalEvaluatedResolvent (x : Fin 2 → ℕ) :
    Polynomial RootRing :=
  pairEvaluatedResolvent x rootVariables

noncomputable def tripleUniversalEvaluatedResolvent (x : Fin 2 → ℕ) :
    Polynomial RootRing :=
  tripleEvaluatedResolvent x rootVariables

theorem pairUniversalEvaluatedResolvent_monic (x : Fin 2 → ℕ) :
    (pairUniversalEvaluatedResolvent x).Monic :=
  pairEvaluatedResolvent_monic x rootVariables

theorem tripleUniversalEvaluatedResolvent_monic (x : Fin 2 → ℕ) :
    (tripleUniversalEvaluatedResolvent x).Monic :=
  tripleEvaluatedResolvent_monic x rootVariables

theorem pairUniversalEvaluatedResolvent_natDegree (x : Fin 2 → ℕ) :
    (pairUniversalEvaluatedResolvent x).natDegree = 15 :=
  pairEvaluatedResolvent_natDegree x rootVariables

theorem tripleUniversalEvaluatedResolvent_natDegree (x : Fin 2 → ℕ) :
    (tripleUniversalEvaluatedResolvent x).natDegree = 10 :=
  tripleEvaluatedResolvent_natDegree x rootVariables

theorem pairUniversalEvaluatedResolvent_rename
    (x : Fin 2 → ℕ) (g : S6) :
    (pairUniversalEvaluatedResolvent x).map (rename g).toRingHom =
      pairUniversalEvaluatedResolvent x := by
  rw [pairUniversalEvaluatedResolvent, pairEvaluatedResolvent_map]
  have hroot : (fun i ↦ (rename g).toRingHom (rootVariables i)) =
      fun i ↦ rootVariables (g i) := by
    funext i
    simp [rootVariables]
  rw [hroot, pairEvaluatedResolvent_permute]

theorem tripleUniversalEvaluatedResolvent_rename
    (x : Fin 2 → ℕ) (g : S6) :
    (tripleUniversalEvaluatedResolvent x).map (rename g).toRingHom =
      tripleUniversalEvaluatedResolvent x := by
  rw [tripleUniversalEvaluatedResolvent, tripleEvaluatedResolvent_map]
  have hroot : (fun i ↦ (rename g).toRingHom (rootVariables i)) =
      fun i ↦ rootVariables (g i) := by
    funext i
    simp [rootVariables]
  rw [hroot, tripleEvaluatedResolvent_permute]

theorem pairUniversalEvaluatedResolvent_coefficient_isSymmetric
    (x : Fin 2 → ℕ) (n : ℕ) :
    ((pairUniversalEvaluatedResolvent x).coeff n).IsSymmetric := by
  intro g
  have h := congrArg
    (fun P : Polynomial RootRing ↦ P.coeff n)
    (pairUniversalEvaluatedResolvent_rename x g)
  simp only [Polynomial.coeff_map] at h
  change (rename g).toRingHom
      ((pairUniversalEvaluatedResolvent x).coeff n) =
    (pairUniversalEvaluatedResolvent x).coeff n
  exact h

theorem tripleUniversalEvaluatedResolvent_coefficient_isSymmetric
    (x : Fin 2 → ℕ) (n : ℕ) :
    ((tripleUniversalEvaluatedResolvent x).coeff n).IsSymmetric := by
  intro g
  have h := congrArg
    (fun P : Polynomial RootRing ↦ P.coeff n)
    (tripleUniversalEvaluatedResolvent_rename x g)
  simp only [Polynomial.coeff_map] at h
  change (rename g).toRingHom
      ((tripleUniversalEvaluatedResolvent x).coeff n) =
    (tripleUniversalEvaluatedResolvent x).coeff n
  exact h

noncomputable def pairSymmetricCoefficient
    (x : Fin 2 → ℕ) (n : ℕ) :
    MvPolynomial.symmetricSubalgebra (Fin 6) ℤ :=
  ⟨(pairUniversalEvaluatedResolvent x).coeff n,
    pairUniversalEvaluatedResolvent_coefficient_isSymmetric x n⟩

noncomputable def tripleSymmetricCoefficient
    (x : Fin 2 → ℕ) (n : ℕ) :
    MvPolynomial.symmetricSubalgebra (Fin 6) ℤ :=
  ⟨(tripleUniversalEvaluatedResolvent x).coeff n,
    tripleUniversalEvaluatedResolvent_coefficient_isSymmetric x n⟩

noncomputable def pairElementaryCoefficient
    (x : Fin 2 → ℕ) (n : ℕ) : RootRing :=
  (MvPolynomial.esymmAlgEquiv (Fin 6) ℤ (by simp)).symm
    (pairSymmetricCoefficient x n)

noncomputable def tripleElementaryCoefficient
    (x : Fin 2 → ℕ) (n : ℕ) : RootRing :=
  (MvPolynomial.esymmAlgEquiv (Fin 6) ℤ (by simp)).symm
    (tripleSymmetricCoefficient x n)

theorem esymmAlgEquiv_pairElementaryCoefficient
    (x : Fin 2 → ℕ) (n : ℕ) :
    MvPolynomial.esymmAlgEquiv (Fin 6) ℤ (by simp)
        (pairElementaryCoefficient x n) = pairSymmetricCoefficient x n := by
  exact (MvPolynomial.esymmAlgEquiv (Fin 6) ℤ (by simp)).apply_symm_apply _

theorem esymmAlgEquiv_tripleElementaryCoefficient
    (x : Fin 2 → ℕ) (n : ℕ) :
    MvPolynomial.esymmAlgEquiv (Fin 6) ℤ (by simp)
        (tripleElementaryCoefficient x n) = tripleSymmetricCoefficient x n := by
  exact (MvPolynomial.esymmAlgEquiv (Fin 6) ℤ (by simp)).apply_symm_apply _

theorem pairUniversalEvaluatedResolvent_coefficient_eq_aeval_esymm
    (x : Fin 2 → ℕ) (n : ℕ) :
    (pairUniversalEvaluatedResolvent x).coeff n =
      MvPolynomial.aeval
        (fun i : Fin 6 ↦ MvPolynomial.esymm (Fin 6) ℤ (i + 1))
        (pairElementaryCoefficient x n) := by
  have h := congrArg Subtype.val
    (esymmAlgEquiv_pairElementaryCoefficient x n)
  simpa only [MvPolynomial.esymmAlgEquiv_apply,
    MvPolynomial.esymmAlgHom_apply, pairSymmetricCoefficient] using h.symm

theorem tripleUniversalEvaluatedResolvent_coefficient_eq_aeval_esymm
    (x : Fin 2 → ℕ) (n : ℕ) :
    (tripleUniversalEvaluatedResolvent x).coeff n =
      MvPolynomial.aeval
        (fun i : Fin 6 ↦ MvPolynomial.esymm (Fin 6) ℤ (i + 1))
        (tripleElementaryCoefficient x n) := by
  have h := congrArg Subtype.val
    (esymmAlgEquiv_tripleElementaryCoefficient x n)
  simpa only [MvPolynomial.esymmAlgEquiv_apply,
    MvPolynomial.esymmAlgHom_apply, tripleSymmetricCoefficient] using h.symm

section Specialization

variable {K : Type*} [CommRing K]

theorem pairUniversalEvaluatedResolvent_specialize
    (x : Fin 2 → ℕ) (r : Fin 6 → K) :
    (pairUniversalEvaluatedResolvent x).map
        (MvPolynomial.eval₂Hom (Int.castRingHom K) r) =
      pairEvaluatedResolvent x r := by
  rw [pairUniversalEvaluatedResolvent, pairEvaluatedResolvent_map]
  congr 2
  funext i
  simp [rootVariables]

theorem tripleUniversalEvaluatedResolvent_specialize
    (x : Fin 2 → ℕ) (r : Fin 6 → K) :
    (tripleUniversalEvaluatedResolvent x).map
        (MvPolynomial.eval₂Hom (Int.castRingHom K) r) =
      tripleEvaluatedResolvent x r := by
  rw [tripleUniversalEvaluatedResolvent, tripleEvaluatedResolvent_map]
  congr 2
  funext i
  simp [rootVariables]

theorem pairEvaluatedResolvent_coefficient_eq
    (x : Fin 2 → ℕ) (r : Fin 6 → K) (n : ℕ) :
    (pairEvaluatedResolvent x r).coeff n =
      MvPolynomial.eval₂ (Int.castRingHom K) r
        (MvPolynomial.aeval
          (fun i : Fin 6 ↦ MvPolynomial.esymm (Fin 6) ℤ (i + 1))
          (pairElementaryCoefficient x n)) := by
  rw [← pairUniversalEvaluatedResolvent_specialize x r,
    Polynomial.coeff_map,
    pairUniversalEvaluatedResolvent_coefficient_eq_aeval_esymm]
  simp only [MvPolynomial.coe_eval₂Hom]

theorem tripleEvaluatedResolvent_coefficient_eq
    (x : Fin 2 → ℕ) (r : Fin 6 → K) (n : ℕ) :
    (tripleEvaluatedResolvent x r).coeff n =
      MvPolynomial.eval₂ (Int.castRingHom K) r
        (MvPolynomial.aeval
          (fun i : Fin 6 ↦ MvPolynomial.esymm (Fin 6) ℤ (i + 1))
          (tripleElementaryCoefficient x n)) := by
  rw [← tripleUniversalEvaluatedResolvent_specialize x r,
    Polynomial.coeff_map,
    tripleUniversalEvaluatedResolvent_coefficient_eq_aeval_esymm]
  simp only [MvPolynomial.coe_eval₂Hom]

end Specialization

end LeanProofs.PolynomialFormulas.SexticEvaluatedResolvents
