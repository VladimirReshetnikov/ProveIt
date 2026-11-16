module
public import M6PA.Theory
public import M6PA.Calibration.RelationalClosedCertificatePrimitives
public import M6PA.Calibration.RelationalOrderIsoReflexivity
public import M6PA.Calibration.RelationalOrderIsoClosedSymmetry
public import M6PA.Calibration.RelationalMultiplicationCoherenceSupplier
@[expose] public section
namespace M6.PA.RelationalClosedCertificate
open FFL FFL.FirstOrder RelationalSource ND PairGraph
attribute [local irreducible] Ordinal.domain orderIso
private theorem isoRefl_shift : Rewriting.shift orderIsoReflexivityStatement=orderIsoReflexivityStatement := by
  change Semiformula.rewAux Rew.shift _ = _
  simp only [orderIsoReflexivityStatement,Semiformula.rewAux,Semiformula.imp_eq,
    Semiformula.neg_eq,coherenceRewNeg,Ordinal.domain_rew,orderIso_rew]
  finishSourceSyntax
private theorem isoSymm_shift : Rewriting.shift isoSymmetryClosed=isoSymmetryClosed := by
  rw [isoSymmetryClosed_eq]
  change Semiformula.rewAux Rew.shift _ = _
  simp only [Semiformula.rewAux,Semiformula.imp_eq,Semiformula.neg_eq,
    coherenceRewNeg,Ordinal.domain_rew,orderIso_rew]
  finishSourceSyntax
private theorem isoTrans_shift : Rewriting.shift isoTransitivityClosed=isoTransitivityClosed := by
  rw [isoTransitivityClosed_eq]
  change Semiformula.rewAux Rew.shift _ = _
  simp only [Semiformula.rewAux,Semiformula.imp_eq,Semiformula.neg_eq,
    coherenceRewNeg,Ordinal.domain_rew,orderIso_rew]
  finishSourceSyntax
private theorem addCoherence_shift : Rewriting.shift addCoherenceStatement=addCoherenceStatement := by
  simp only [addCoherenceStatement]
  coherenceInductionSyntax
private theorem mulCoherence_shift : Rewriting.shift mulCoherenceStatement=mulCoherenceStatement := by
  simp only [mulCoherenceStatement]
  mulCoherenceInductionSyntax

theorem isoReflexivity_closed : orderIsoReflexivityStatement.freeVariables=∅ :=
  Semiformula.freeVariables_eq_empty_of_shift_eq isoRefl_shift
theorem isoSymmetry_closed : isoSymmetryClosed.freeVariables=∅ :=
  Semiformula.freeVariables_eq_empty_of_shift_eq isoSymm_shift
theorem isoTransitivity_closed : isoTransitivityClosed.freeVariables=∅ :=
  Semiformula.freeVariables_eq_empty_of_shift_eq isoTrans_shift
theorem addCoherence_closed : addCoherenceStatement.freeVariables=∅ :=
  Semiformula.freeVariables_eq_empty_of_shift_eq addCoherence_shift
theorem mulCoherence_closed : mulCoherenceStatement.freeVariables=∅ :=
  Semiformula.freeVariables_eq_empty_of_shift_eq mulCoherence_shift
#print axioms isoReflexivity_closed
#print axioms isoSymmetry_closed
#print axioms isoTransitivity_closed
#print axioms addCoherence_closed
#print axioms mulCoherence_closed
end M6.PA.RelationalClosedCertificate
