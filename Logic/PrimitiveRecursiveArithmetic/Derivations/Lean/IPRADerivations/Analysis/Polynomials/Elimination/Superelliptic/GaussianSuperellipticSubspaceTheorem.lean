import IPRADerivations.Analysis.LinearAlgebra.Cofactors.GaussianRationalAnnihilatorVector
import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.GaussianSuperellipticSubspaceFromSpan

/-!
# The superelliptic subspace bound from computed rank deficiency

The same numerical matrix supplies the point memberships and drives
the column elimination. Strict deficiency of its pivot count produces
an actual nonzero null vector. The compiled polynomial for that vector
then gives the original weighted norm bound.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSuperellipticSubspaceTheorem

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianSuperellipticSubspaceWitness (curveInput basisCount points)
open GaussianSuperellipticSubspaceFromSpan (pointMembership subspace_witness_bound)
open GaussianRationalAnnihilatorVector (certificate returned_certificate)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def annihilator (f m c L A R : PTm n) : PTm n :=
  GaussianRationalAnnihilatorVector.run A R (basisCount f m c L)

def input (f m c L A R : PTm n) : Fm PTm n := curveInput f m c ⋏
  GaussianRationalAnnihilatorVector.input A R (basisCount f m c L)

@[simp] theorem subst_annihilator {k : ℕ} (σ : Fin n → PTm k) (f m c L A R : PTm n) :
    Syn.subst σ (annihilator f m c L A R) = annihilator (Syn.subst σ f) (Syn.subst σ m)
      (Syn.subst σ c) (Syn.subst σ L) (Syn.subst σ A) (Syn.subst σ R) := by simp [annihilator]

@[simp] theorem subst_input {k : ℕ} (σ : Fin n → PTm k) (f m c L A R : PTm n) :
    (input f m c L A R).subst σ = input (Syn.subst σ f) (Syn.subst σ m)
      (Syn.subst σ c) (Syn.subst σ L) (Syn.subst σ A) (Syn.subst σ R) := by simp [input]

theorem computed_annihilator (f m c L A R : PTm n) (h : Γ ⊢[PRAAx] input f m c L A R) : Γ ⊢[PRAAx]
    certificate A R (basisCount f m c L) (annihilator f m c L A R) :=
  returned_certificate A R (basisCount f m c L) (.andE₂ h)

theorem subspace_bound (f m c L P A R : PTm n) (h : Γ ⊢[PRAAx] input f m c L A R)
    (hPts : Γ ⊢[PRAAx] points f m P) (hSpan : Γ ⊢[PRAAx] pointMembership f m c L P A R) :
    Γ ⊢[PRAAx] le (length P) L := by
  let a := annihilator f m c L A R
  have actual := computed_annihilator f m c L A R h
  have finite : Γ ⊢[PRAAx] GaussianRationalFreeColumnVector.nonzeroVector a (basisCount f m c L) :=
    .andE₁ (.andE₂ actual)
  have nonzero : Γ ⊢[PRAAx] GaussianAnnihilatorPolynomial.nonzeroLambda a m
      (GaussianRationalPolynomialDegree.degree f c) L := by
    simpa only [GaussianAnnihilatorPolynomial.nonzeroLambda,GaussianRationalFreeColumnVector.nonzeroVector,
      basisCount,Syn.shift,GaussianWeightedMonomialBasis.subst_count,GaussianRationalPolynomialDegree.subst_degree] using finite
  have vectorInput : Γ ⊢[PRAAx] GaussianSuperellipticSubspaceWitness.input f a m c L :=
    .andI (.andE₁ h) (.andI (.andE₁ actual) nonzero)
  exact subspace_witness_bound f a m c L P A R vectorInput hPts (.andE₂ (.andE₂ actual)) hSpan

theorem actual_computed_annihilator_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      certificate (var 4) (var 5) (basisCount (var 0) (var 1) (var 2) (var 3))
        (annihilator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (computed_annihilator _ _ _ _ _ _ Prf.hyp0))

theorem actual_subspace_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 5) (var 6) ⟶ points (var 0) (var 1) (var 4) ⟶
      pointMembership (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶ le (length (var 4)) (var 3)) :=
  closeUniv 7 (.impI (.impI (.impI (subspace_bound _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianSuperellipticSubspaceTheorem
