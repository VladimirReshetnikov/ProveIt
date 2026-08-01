import PolynomialFormulas.ComputableDummitCoefficients

/-!
# Certified executable coefficients of Dummit's sextic

This file connects the directly evaluable sparse table to the abstract
symmetric-polynomial coefficients and transfers primitive recursiveness.
-/

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

open QuinticRadicalDecidability
open QuinticRadicalDecidability.MonicQuintic

theorem elementaryTuple_eq_scalarEsymm {R : Type*} [CommRing R]
    (x : Fin 5 → R) (i : Fin 5) :
    elementaryTuple x i = scalarEsymm (List.ofFn x) (i + 1) := by
  fin_cases i <;>
    simp [elementaryTuple, scalarEsymm, List.ofFn_succ] <;>
    ring

theorem elementaryTuple_eq_multiset_esymm {R : Type*} [CommRing R]
    (x : Fin 5 → R) (i : Fin 5) :
    elementaryTuple x i =
      (Finset.univ.val.map x).esymm (i + 1) := by
  rw [elementaryTuple_eq_scalarEsymm,
    scalarEsymm_eq_multiset_esymm, ← Fin.univ_val_map]

theorem elementaryTuple_X :
    elementaryTuple
        (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) ℤ) =
      fun i : Fin 5 ↦ MvPolynomial.esymm (Fin 5) ℤ (i + 1) := by
  funext i
  calc
    elementaryTuple
        (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) ℤ) i =
        (Finset.univ.val.map
          (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) ℤ)).esymm
            (i + 1) := elementaryTuple_eq_multiset_esymm _ _
    _ = MvPolynomial.aeval
          (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) ℤ)
      (MvPolynomial.esymm (Fin 5) ℤ (i + 1)) :=
      (MvPolynomial.aeval_esymm_eq_multiset_esymm
        (S := MvPolynomial (Fin 5) ℤ) (Fin 5) ℤ (i + 1)
        (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) ℤ)).symm
    _ = MvPolynomial.esymm (Fin 5) ℤ (i + 1) := by simp

theorem scalarResolvent_X :
    FrobeniusDummitResolvent.scalarResolvent
        (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) ℤ) =
      FrobeniusDummitResolvent.universalResolvent := by
  rw [FrobeniusDummitResolvent.scalarResolvent]
  have heval :
      MvPolynomial.eval₂Hom
          (Int.castRingHom (MvPolynomial (Fin 5) ℤ)) MvPolynomial.X =
        RingHom.id (MvPolynomial (Fin 5) ℤ) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp
    · intro i
      simp
  simp [heval]

theorem toMvPolynomial_dummitTable_eq_elementaryResolventCoefficient
    (n : Fin 7) :
    SparsePolynomial.toMvPolynomial (dummitTable n) =
      FrobeniusDummitResolvent.elementaryResolventCoefficient n := by
  apply (MvPolynomial.esymmAlgEquiv (Fin 5) ℤ (by simp)).injective
  rw [FrobeniusDummitResolvent.esymmAlgEquiv_elementaryResolventCoefficient]
  apply Subtype.ext
  simp only [MvPolynomial.esymmAlgEquiv_apply,
    MvPolynomial.esymmAlgHom_apply,
    FrobeniusDummitResolvent.symmetricResolventCoefficient]
  have h := dummitTable_eval_elementaryTuple
    (R := MvPolynomial (Fin 5) ℤ) n MvPolynomial.X
  rw [eval_eq_eval₂_toMvPolynomial, elementaryTuple_X,
    listRootCoefficient_eq_scalarResolvent_coeff, scalarResolvent_X] at h
  change MvPolynomial.aeval
      (fun i : Fin 5 ↦ MvPolynomial.esymm (Fin 5) ℤ (i + 1))
      (SparsePolynomial.toMvPolynomial (dummitTable n)) =
    FrobeniusDummitResolvent.universalResolvent.coeff n
  rw [MvPolynomial.aeval_def]
  change MvPolynomial.eval₂
      (Int.castRingHom (MvPolynomial (Fin 5) ℤ))
      (fun i : Fin 5 ↦ MvPolynomial.esymm (Fin 5) ℤ (i + 1))
      (SparsePolynomial.toMvPolynomial (dummitTable n)) =
    FrobeniusDummitResolvent.universalResolvent.coeff n
  exact h

theorem explicitDummitCoefficients_eq_dummitCoefficients
    (f : MonicQuintic) :
    explicitDummitCoefficients f =
      QuinticDummitCoefficients.dummitCoefficients f := by
  funext n
  rw [explicitDummitCoefficients,
    QuinticDummitCoefficients.dummitCoefficients,
    eval_eq_eval₂_toMvPolynomial,
    toMvPolynomial_dummitTable_eq_elementaryResolventCoefficient]
  rfl

theorem explicitDummitCoefficients_apply_primrec (n : Fin 7) :
    Primrec fun f : MonicQuintic ↦ explicitDummitCoefficients f n := by
  exact (QuinticDummitCoefficients.dummitCoefficients_apply_primrec n).of_eq
    fun f ↦ congrFun
      (explicitDummitCoefficients_eq_dummitCoefficients f).symm n

theorem explicitDummitCoefficients_primrec :
    Primrec explicitDummitCoefficients := by
  apply Primrec.fin_curry.mpr
  have h : Primrec₂ fun n : Fin 7 ↦ fun f : MonicQuintic ↦
      explicitDummitCoefficients f n :=
    Primrec.fin_curry₁.mpr explicitDummitCoefficients_apply_primrec
  exact h.swap

@[simp] theorem explicitDummitCoefficients_six (f : MonicQuintic) :
    explicitDummitCoefficients f 6 = 1 := by
  rw [explicitDummitCoefficients_eq_dummitCoefficients]
  exact QuinticDummitCoefficients.dummitCoefficients_six f

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients
