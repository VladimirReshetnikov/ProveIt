module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.RelationalClosedCertificateCoherenceSupport
public import M6PA.Calibration.PAInterpretedParameterClosure
public import M6PA.Calibration.RelationalOrderIsoSuccessorSupplier
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.RelationalClosedCertificate
open FFL FFL.FirstOrder RelationalSource ND PairGraph ForwardRelational
attribute [local irreducible] Ordinal.domain Ordinal.successor orderIso

def successorIsoClosed : Form := closeParameters 4 (orderIsoSuccessorStatement 3 2 1 0)
theorem successorIsoClosed_eq : successorIsoClosed=∀¹ ∀¹ ∀¹ ∀¹
    ((Ordinal.domain (.bvar 3) ⋏ (Ordinal.domain (.bvar 2) ⋏
      (Ordinal.successor (.bvar 3) (.bvar 1) ⋏
        (Ordinal.successor (.bvar 2) (.bvar 0) ⋏ orderIso (.bvar 3) (.bvar 2))))) 🡒
      orderIso (.bvar 1) (.bvar 0)) := by
  simp only [successorIsoClosed,closeParameters,closeParameter,orderIsoSuccessorStatement,
    orderIsoSuccessorPremise,Semiformula.rewAux,Semiformula.imp_eq,Semiformula.neg_eq,coherenceRewNeg,
    Ordinal.domain_rew,Ordinal.successor_rew,orderIso_rew]
  finishSourceSyntax

theorem successorIso_closed : successorIsoClosed.freeVariables=∅ := by
  apply Semiformula.freeVariables_eq_empty_of_shift_eq
  rw [successorIsoClosed_eq]
  change Semiformula.rewAux Rew.shift _ = _
  simp only [Semiformula.rewAux,Semiformula.imp_eq,Semiformula.neg_eq,coherenceRewNeg,
    Ordinal.domain_rew,Ordinal.successor_rew,orderIso_rew]
  finishSourceSyntax
#print axioms successorIsoClosed_eq
#print axioms successorIso_closed
end PA196.Arithmetic.Transport.RelationalClosedCertificate
