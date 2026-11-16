module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationND
public import M6PA.Calibration.PAInterpretedReflexivity
public import M6PA.Calibration.PAInterpretedSymmetry
public import M6PA.Calibration.PAInterpretedTransitivity
public import M6PA.Calibration.PAInterpretedFunctionCongruenceBinaryImage
public import M6PA.Calibration.PAInterpretedFunctionCongruenceSuccImage
public import M6PA.Calibration.PAInterpretedArithmeticZeroImage
public import M6PA.Calibration.PAInterpretedZeroNotSucc
public import M6PA.Calibration.PAInterpretedSuccInjective
public import M6PA.Calibration.PAInterpretedMulSuccSupplier
@[expose] public section

/-! Exhaustive constructive assembly of all twelve literal fixed PAeq images.
The dispatch uses decidable syntax equality, not elimination of Prop-only
axiom membership into proof data. No induction or parameter closure is claimed. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

structure FixedImagePremises (Γ : List Form) where
  multiplication : MultiplicationImagePremises Γ
  totality : TotalityPremises Γ
  strictSeparation : ND.Proof Γ closedStrictSeparation

def interpretedFixedAxiom {Γ : List Form} (I : FixedImagePremises Γ)
    (p : SourceFormula 0) (hp : p ∈ Presentation.fixedAxioms) (f : Nat → Term 0) :
    ND.Proof Γ (formula p Fin.elim0 f) := by
  let A := I.multiplication.additionImage
  by_cases h0 : p = Presentation.reflexivity
  · subst p; exact interpretedReflexivity A.coherence.equality A.identity f
  by_cases h1 : p = Presentation.symmetry
  · subst p; exact interpretedSymmetry A.symmetry f
  by_cases h2 : p = Presentation.transitivity
  · subst p; exact interpretedTransitivity A.coherence.equality I.multiplication.transitivity f
  by_cases h3 : p = Presentation.succCongruence
  · subst p; exact interpretedSuccCongruence A.coherence I.totality f
  by_cases h4 : p = Presentation.addCongruence
  · subst p; exact interpretedAddCongruence A.coherence I.totality f
  by_cases h5 : p = Presentation.mulCongruence
  · subst p; exact interpretedMulCongruence A.coherence I.totality f
  by_cases h6 : p = Presentation.addZero
  · subst p; exact interpretedAddZero A.coherence I.totality A.identity f
  by_cases h7 : p = Presentation.addSucc
  · subst p; exact interpretedAddSucc A I.totality f
  by_cases h8 : p = Presentation.mulZero
  · subst p; exact interpretedMulZero A.coherence I.totality A.identity f
  by_cases h9 : p = Presentation.mulSucc
  · subst p; exact interpretedMulSucc I.multiplication I.totality f
  by_cases h10 : p = Presentation.zeroNotSucc
  · subst p; exact interpretedZeroNotSucc A.coherence.equality f
  by_cases h11 : p = Presentation.succInjective
  · subst p; exact interpretedSuccInjective A.coherence.equality I.strictSeparation f
  simp [Presentation.fixedAxioms,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11] at hp

#print axioms interpretedFixedAxiom
end M6.PA.ForwardRelational

