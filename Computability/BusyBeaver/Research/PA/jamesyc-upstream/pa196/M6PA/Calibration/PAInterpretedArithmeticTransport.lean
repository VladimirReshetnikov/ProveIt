module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalCoherenceWitnesses
public import M6PA.Calibration.PAInterpretedEqualityWitnesses
@[expose] public section

/-! Ordinary endpoint transport for the unchanged arithmetic graph predicates. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] PairGraph.addResult PairGraph.mulResult Ordinal.successor
set_option maxHeartbeats 800000

macro "arithmeticValueSyntax" : tactic => `(tactic|
  ((try simp only [BinaryOperation.result_rew]) <;> (try interpretedWitnessSyntax) <;>
    (try simp only [BinaryOperation.result_rew]) <;> (try interpretedWitnessSyntax)))

def binaryInputsTransport {Γ : List Form} (E : FormulaEquality Γ) (op : BinaryOperation)
    (a a' b b' z : Term 0) (ha : ND.Proof Γ (ND.eq a a')) (hb : ND.Proof Γ (ND.eq b b'))
    (h : ND.Proof Γ (op.result a b z)) : ND.Proof Γ (op.result a' b' z) := by
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![a])
      (op.result (.bvar 0) (Rew.bShift b) (Rew.bShift z))) := by
    convert h using 1 <;> (cases op <;> simp only [BinaryOperation.result] <;> totalitySyntax)
  have mid := E.substituteOne (op.result (.bvar 0) (Rew.bShift b) (Rew.bShift z)) a a' ha hp
  have hm : ND.Proof Γ (op.result a' b z) := by
    convert mid using 1 <;> (cases op <;> simp only [BinaryOperation.result] <;> totalitySyntax)
  have hq : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![b])
      (op.result (Rew.bShift a') (.bvar 0) (Rew.bShift z))) := by
    convert hm using 1 <;> (cases op <;> simp only [BinaryOperation.result] <;> totalitySyntax)
  have out := E.substituteOne (op.result (Rew.bShift a') (.bvar 0) (Rew.bShift z)) b b' hb hq
  convert out using 1 <;> (cases op <;> simp only [BinaryOperation.result] <;> totalitySyntax)

def successorInputTransport {Γ : List Form} (E : FormulaEquality Γ) (a a' z : Term 0)
    (ha : ND.Proof Γ (ND.eq a a')) (h : ND.Proof Γ (Ordinal.successor a z)) :
    ND.Proof Γ (Ordinal.successor a' z) := by
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![a])
      (Ordinal.successor (.bvar 0) (Rew.bShift z))) := by
    convert h using 1 <;> interpretedWitnessSyntax
  have out := E.substituteOne (Ordinal.successor (.bvar 0) (Rew.bShift z)) a a' ha hp
  convert out using 1 <;> interpretedWitnessSyntax

#print axioms binaryInputsTransport
#print axioms successorInputTransport
end M6.PA.ForwardRelational
