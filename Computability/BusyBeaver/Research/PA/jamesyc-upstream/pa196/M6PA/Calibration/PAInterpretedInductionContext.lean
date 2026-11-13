module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedInductionParameters
public import M6PA.Calibration.PAInterpretedAddSuccSupplier
public import M6PA.Calibration.RelationalOrderIsoClosedTransitivity
@[expose] public section

/-! A finite context and finite guarded conclusion for the arbitrary induction
image. No free parameter's domain is silently supplied or generalized. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

def interpretedInductionAxioms (p : SourceFormula 1) (ρ : Nat → Term 0) : List Form :=
  separationFormula (∼inductionPredicate p ρ)::Ordinal.intersectionFormula::
    isoTransitivityClosed::interpretedAddSuccAxioms

def interpretedInductionPremises (p : SourceFormula 1) (ρ : Nat → Term 0) :
    SubstitutionPremises (interpretedInductionAxioms p ρ) := by
  let I := ((interpretedAddSuccPremises.up isoTransitivityClosed).up Ordinal.intersectionFormula).up
    (separationFormula (∼inductionPredicate p ρ))
  let T0 := ((functionCongruenceTotality.up isoSymmetryClosed).up closedInclusiveSeparation).up identityStatement
  let T := ((T0.up isoTransitivityClosed).up Ordinal.intersectionFormula).up
    (separationFormula (∼inductionPredicate p ρ))
  exact ⟨I.coherence,T,I.identity,I.symmetry,assumption (by simp [interpretedInductionAxioms])⟩

def interpretedInductionGuarded (p : SourceFormula 1) (ρ : Nat → Term 0) : Form :=
  inductionParameterGuard (p.freeVariables.sort (· ≤ ·)) ρ 🡒
    formula (Presentation.inductionFormula p) Fin.elim0 ρ

def interpretedInductionDerivation (p : SourceFormula 1) (ρ : Nat → Term 0) :
    ND.Proof (interpretedInductionAxioms p ρ) (interpretedInductionGuarded p ρ) := by
  apply impIntro
  let g := inductionParameterGuard (p.freeVariables.sort (· ≤ ·)) ρ
  let A := (interpretedInductionPremises p ρ).up g
  exact interpretedInduction A p ρ
    (inductionGuardCoverage p ρ (assumption (by simp [g])))
    (assumption (by simp [interpretedInductionAxioms])) A.coherence.adjunction
    (assumption (by simp [interpretedInductionAxioms]))

#print axioms interpretedInductionPremises
#print axioms interpretedInductionDerivation
end M6.PA.ForwardRelational

