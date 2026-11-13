module
public import M6PA.Theory
public import M6PA.Calibration.RelationalClosedCertificateCoherenceZero
public import M6PA.Calibration.PAInterpretedVariableEqualityTransport
@[expose] public section
namespace M6.PA.RelationalClosedCertificate
open FFL FFL.FirstOrder RelationalSource ND PairGraph ForwardRelational
attribute [local irreducible] orderIso

def isoTransportOpen : Form :=
  (orderIso (.fvar 3) (.fvar 2) ⋏ (ND.eq (.fvar 1) (.fvar 3) ⋏ ND.eq (.fvar 0) (.fvar 2))) 🡒
    orderIso (.fvar 1) (.fvar 0)
def isoTransportDerivation : ND.Proof zeroIsoAxioms isoTransportOpen := by
  apply impIntro
  let premise : Form := orderIso (.fvar 3) (.fvar 2) ⋏
    (ND.eq (.fvar 1) (.fvar 3) ⋏ ND.eq (.fvar 0) (.fvar 2))
  let E : FormulaEquality (premise::zeroIsoAxioms) :=
    ⟨⟨assumption (by simp [zeroIsoAxioms]),assumption (by simp [zeroIsoAxioms]),
      assumption (by simp [zeroIsoAxioms])⟩,assumption (by simp [zeroIsoAxioms])⟩
  have hp : ND.Proof (premise::zeroIsoAxioms) premise := assumption (by simp)
  exact interpretedIsoTransport E (.fvar 3) (.fvar 1) (.fvar 2) (.fvar 0)
    (E.symmetryOf (andLeft (andRight hp))) (E.symmetryOf (andRight (andRight hp))) (andLeft hp)
def isoTransportClosed : Form := closeParameters 4 isoTransportOpen

theorem isoTransportClosed_eq : isoTransportClosed=∀¹ ∀¹ ∀¹ ∀¹
    ((orderIso (.bvar 3) (.bvar 2) ⋏ (ND.eq (.bvar 1) (.bvar 3) ⋏ ND.eq (.bvar 0) (.bvar 2))) 🡒
      orderIso (.bvar 1) (.bvar 0)) := by
  simp only [isoTransportClosed,closeParameters,closeParameter,isoTransportOpen,
    Semiformula.rewAux,Semiformula.imp_eq,Semiformula.neg_eq,coherenceRewNeg,orderIso_rew,ND.eq]
  finishSourceSyntax

theorem isoTransport_closed : isoTransportClosed.freeVariables=∅ := by
  apply Semiformula.freeVariables_eq_empty_of_shift_eq
  rw [isoTransportClosed_eq]
  change Semiformula.rewAux Rew.shift _ = _
  simp only [Semiformula.rewAux,Semiformula.imp_eq,Semiformula.neg_eq,coherenceRewNeg,orderIso_rew,ND.eq]
  finishSourceSyntax
#print axioms isoTransportDerivation
#print axioms isoTransportClosed_eq
#print axioms isoTransport_closed
end M6.PA.RelationalClosedCertificate
