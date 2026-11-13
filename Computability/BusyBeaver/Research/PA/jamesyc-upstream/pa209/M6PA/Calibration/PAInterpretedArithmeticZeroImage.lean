module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedArithmeticZeroEquality
public import M6PA.Calibration.PAInterpretedFunctionCongruenceGuards
public import M6PA.Calibration.PAInterpretedUniversal
public import M6PA.Calibration.PAPresentationAxioms
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain

def arithmeticZeroSource (op : BinaryOperation) : SourceFormula 0 :=
  .all (Presentation.eq (op.term Presentation.zero (.bvar 0)) (arithmeticZeroRight op 0))

def interpretedArithmeticZero {Γ : List Form} (op : BinaryOperation)
    (A : CoherencePremises Γ) (T : TotalityPremises Γ)
    (hid : ND.Proof Γ PairGraph.identityStatement) (f : Nat → Term 0) :
    ND.Proof Γ (formula (arithmeticZeroSource op) Fin.elim0 f) := by
  apply interpretedAllIntro
  change ND.Proof (functionGuardContext 1 Γ)
    (equal (op.term Presentation.zero (.bvar 0)) (arithmeticZeroRight op 0)
      (functionBoundEnv 1) (freeShiftEnv f))
  exact arithmeticZeroVariablesEqual (functionGuardCoherence A 1).equality
    (up (PairGraph.rightSuccessorIdentityShift hid) (Ordinal.domain (.fvar 0)))
    (functionGuardTotality T 1) op 0 _ _ (functionGuardDomain 1 0)

def interpretedAddZero {Γ : List Form} (A : CoherencePremises Γ) (T : TotalityPremises Γ)
    (hid : ND.Proof Γ PairGraph.identityStatement) (f : Nat → Term 0) :
    ND.Proof Γ (formula Presentation.addZero Fin.elim0 f) :=
  interpretedArithmeticZero .addition A T hid f

def interpretedMulZero {Γ : List Form} (A : CoherencePremises Γ) (T : TotalityPremises Γ)
    (hid : ND.Proof Γ PairGraph.identityStatement) (f : Nat → Term 0) :
    ND.Proof Γ (formula Presentation.mulZero Fin.elim0 f) :=
  interpretedArithmeticZero .multiplication A T hid f

#print axioms interpretedAddZero
#print axioms interpretedMulZero
end M6.PA.ForwardRelational

