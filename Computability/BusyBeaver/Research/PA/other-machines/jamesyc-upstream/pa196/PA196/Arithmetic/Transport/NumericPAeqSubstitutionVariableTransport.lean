module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.RelationalClosedCertificateCoherenceZero
public import M6PA.Calibration.PAInterpretedVariableEqualityTransport
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.RelationalClosedCertificate
open FFL FFL.FirstOrder RelationalSource ND PairGraph ForwardRelational
attribute [local irreducible] orderIso

def isoRightTransportOpen : Form :=
  (orderIso (.fvar 2) (.fvar 1) ⋏ ND.eq (.fvar 0) (.fvar 1)) 🡒 orderIso (.fvar 2) (.fvar 0)
def isoRightTransportDerivation : ND.Proof zeroIsoAxioms isoRightTransportOpen := by
  apply impIntro
  let premise : Form := orderIso (.fvar 2) (.fvar 1) ⋏ ND.eq (.fvar 0) (.fvar 1)
  let E : FormulaEquality (premise::zeroIsoAxioms) :=
    ⟨⟨assumption (by simp [zeroIsoAxioms]),assumption (by simp [zeroIsoAxioms]),
      assumption (by simp [zeroIsoAxioms])⟩,assumption (by simp [zeroIsoAxioms])⟩
  have hp : ND.Proof (premise::zeroIsoAxioms) premise := assumption (by simp)
  exact interpretedIsoTransport E (.fvar 2) (.fvar 2) (.fvar 1) (.fvar 0)
    (E.reflexive _) (E.symmetryOf (andRight hp)) (andLeft hp)
def isoRightTransportClosed : Form := closeParameters 3 isoRightTransportOpen

theorem isoRightTransportClosed_eq : isoRightTransportClosed=∀¹ ∀¹ ∀¹
    ((orderIso (.bvar 2) (.bvar 1) ⋏ ND.eq (.bvar 0) (.bvar 1)) 🡒 orderIso (.bvar 2) (.bvar 0)) := by
  simp only [isoRightTransportClosed,closeParameters,closeParameter,isoRightTransportOpen,
    Semiformula.rewAux,Semiformula.imp_eq,Semiformula.neg_eq,coherenceRewNeg,orderIso_rew,ND.eq]
  finishSourceSyntax

theorem isoRightTransport_closed : isoRightTransportClosed.freeVariables=∅ := by
  apply Semiformula.freeVariables_eq_empty_of_shift_eq
  rw [isoRightTransportClosed_eq]
  change Semiformula.rewAux Rew.shift _ = _
  simp only [Semiformula.rewAux,Semiformula.imp_eq,Semiformula.neg_eq,coherenceRewNeg,orderIso_rew,ND.eq]
  finishSourceSyntax
#print axioms isoRightTransportDerivation
#print axioms isoRightTransportClosed_eq
#print axioms isoRightTransport_closed
end PA196.Arithmetic.Transport.RelationalClosedCertificate
