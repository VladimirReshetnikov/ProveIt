module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedFunctionCongruenceBinary
public import M6PA.Calibration.PAInterpretedFunctionCongruenceGuards
public import M6PA.Calibration.PAInterpretedVariableEquality
public import M6PA.Calibration.PAInterpretedUniversal
public import M6PA.Calibration.PAPresentationAxioms
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 800000

/-- Internal finite template: its two instances below name the frozen axioms. -/
def functionBinarySource (op : BinaryOperation) : SourceFormula 0 :=
  .all (.all (.all (.all
    (Presentation.implies (Presentation.eq (.bvar 0) (.bvar 1))
      (Presentation.implies (Presentation.eq (.bvar 2) (.bvar 3))
        (Presentation.eq (op.term (.bvar 0) (.bvar 2)) (op.term (.bvar 1) (.bvar 3))))))))

def interpretedBinaryCongruence {Γ : List Form} (op : BinaryOperation)
    (A : CoherencePremises Γ) (T : TotalityPremises Γ) (f : Nat → Term 0) :
    ND.Proof Γ (formula (functionBinarySource op) Fin.elim0 f) := by
  apply interpretedAllIntro
  apply interpretedAllIntro
  apply interpretedAllIntro
  apply interpretedAllIntro
  let b := functionBoundEnv 4
  let fs := freeShiftEnv (freeShiftEnv (freeShiftEnv (freeShiftEnv f)))
  let e := equal (.bvar 0) (.bvar 1) b fs
  let e' := equal (.bvar 2) (.bvar 3) b fs
  change ND.Proof (functionGuardContext 4 Γ)
    (e 🡒 e' 🡒 equal (op.term (.bvar 0) (.bvar 2)) (op.term (.bvar 1) (.bvar 3)) b fs)
  apply impIntro
  apply impIntro
  let AA := ((functionGuardCoherence A 4).up e).up e'
  let TT := ((functionGuardTotality T 4).up e).up e'
  have hd (i : Fin 4) : ND.Proof (e' :: e :: functionGuardContext 4 Γ) (Ordinal.domain (b i)) :=
    up (up (functionGuardDomain 4 i) e) e'
  have he : ND.Proof (e' :: e :: functionGuardContext 4 Γ) e := assumption (by simp)
  have he' : ND.Proof (e' :: e :: functionGuardContext 4 Γ) e' := assumption (by simp)
  exact binaryVariablesEqual op AA TT 0 1 2 3 b fs (hd 0) (hd 1) (hd 2) (hd 3)
    (boundVariableEqualityIso AA.equality 0 1 b fs he)
    (boundVariableEqualityIso AA.equality 2 3 b fs he')

def interpretedAddCongruence {Γ : List Form}
    (A : CoherencePremises Γ) (T : TotalityPremises Γ) (f : Nat → Term 0) :
    ND.Proof Γ (formula Presentation.addCongruence Fin.elim0 f) :=
  interpretedBinaryCongruence .addition A T f

def interpretedMulCongruence {Γ : List Form}
    (A : CoherencePremises Γ) (T : TotalityPremises Γ) (f : Nat → Term 0) :
    ND.Proof Γ (formula Presentation.mulCongruence Fin.elim0 f) :=
  interpretedBinaryCongruence .multiplication A T f

#print axioms interpretedBinaryCongruence
#print axioms interpretedAddCongruence
#print axioms interpretedMulCongruence
end M6.PA.ForwardRelational

