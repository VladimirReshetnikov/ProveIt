module
public import M6PA.Theory
public import M6PA.Calibration.RelationalClosedCertificate
public import M6PA.Calibration.PAForwardRelationalArithmeticClosure
public import M6PA.Calibration.RelationalMultiplicationUniversalOutput
public import M6PA.Calibration.PAForwardRelationalRewriting
@[expose] public section

namespace M6.PA.RelationalClosedCertificate
open FFL FFL.FirstOrder RelationalSource ND
open PairGraph
attribute [local irreducible] Ordinal.domain Ordinal.zero Ordinal.successor addResult mulResult

private theorem rew_neg {n m : Nat} (τ : Rew language Nat n Nat m) (p : Ordinal.Formula n) :
    Semiformula.rewAux τ p.neg=(Semiformula.rewAux τ p).neg := Semiformula.rewAux_neg τ p

private theorem zero_shift : Rewriting.shift ForwardRelational.zeroInhabited=ForwardRelational.zeroInhabited := by
  change Semiformula.rewAux Rew.shift _ = _
  simp only [ForwardRelational.zeroInhabited,Semiformula.rewAux,Ordinal.domain_rew,Ordinal.zero_rew]
  rfl
private theorem successor_shift : Rewriting.shift ForwardRelational.successorClosed=ForwardRelational.successorClosed := by
  change Semiformula.rewAux Rew.shift _ = _
  simp only [ForwardRelational.successorClosed,closeParameter,Ordinal.domainSuccessorStatement,
    Ordinal.domainSuccessorExists,Semiformula.rewAux,Semiformula.imp_eq,Semiformula.neg_eq,rew_neg,
    Ordinal.domain_rew,Ordinal.successor_rew,Rew.q_comp_bShift_app]
  finishSourceSyntax
private theorem addition_shift : Rewriting.shift addClosedResult=addClosedResult := by
  change Semiformula.rewAux Rew.shift _ = _
  simp only [addClosedResult,closeParameter,addTotalStatement,addOutputConclusion,addOutput,
    Semiformula.rewAux,Semiformula.imp_eq,Semiformula.neg_eq,rew_neg,Ordinal.domain_rew,addResult_rew,
    Rew.q_comp_bShift_app]
  finishSourceSyntax
private theorem multiplication_shift : Rewriting.shift mulUniversalOutput=mulUniversalOutput := by
  change Semiformula.rewAux Rew.shift _ = _
  simp only [mulUniversalOutput,mulResultTotalProperty,mulOutput,sourceImply,
    Semiformula.rewAux,Semiformula.imp_eq,Semiformula.neg_eq,rew_neg,Ordinal.domain_rew,mulResult_rew,
    Rew.q_comp_bShift_app]
  finishSourceSyntax

theorem zero_closed : ForwardRelational.zeroInhabited.freeVariables=∅ := Semiformula.freeVariables_eq_empty_of_shift_eq zero_shift
theorem successor_closed : ForwardRelational.successorClosed.freeVariables=∅ := Semiformula.freeVariables_eq_empty_of_shift_eq successor_shift
theorem addition_closed : addClosedResult.freeVariables=∅ := Semiformula.freeVariables_eq_empty_of_shift_eq addition_shift
theorem multiplication_closed : mulUniversalOutput.freeVariables=∅ := Semiformula.freeVariables_eq_empty_of_shift_eq multiplication_shift

#print axioms zero_closed
#print axioms successor_closed
#print axioms addition_closed
#print axioms multiplication_closed
end M6.PA.RelationalClosedCertificate

