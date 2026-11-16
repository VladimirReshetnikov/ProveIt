module
public import M6PA.Theory
public import M6PA.Calibration.RelationalClosedCertificateCoherenceSupport
public import M6PA.Calibration.PAInterpretedParameterClosure
public import M6PA.Calibration.RelationalZeroIso
@[expose] public section
namespace M6.PA.RelationalClosedCertificate
open FFL FFL.FirstOrder RelationalSource ND PairGraph ForwardRelational
attribute [local irreducible] Ordinal.zero orderIso

def zeroIsoOpen : Form := Ordinal.zero (.fvar 1) 🡒 Ordinal.zero (.fvar 0) 🡒 orderIso (.fvar 1) (.fvar 0)
def zeroIsoAxioms : List Form := [reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula]
def zeroIsoDerivation : ND.Proof zeroIsoAxioms zeroIsoOpen := by
  apply impIntro
  apply impIntro
  apply zeroOrderIso
    (⟨⟨assumption (by simp [zeroIsoAxioms]),assumption (by simp [zeroIsoAxioms]),
      assumption (by simp [zeroIsoAxioms])⟩,assumption (by simp [zeroIsoAxioms])⟩ : FormulaEquality _) 1 0
  · exact assumption (by simp)
  · exact assumption (by simp)
def zeroIsoClosed : Form := closeParameters 2 zeroIsoOpen

theorem zeroIsoClosed_eq : zeroIsoClosed=∀¹ ∀¹
    (Ordinal.zero (.bvar 1) 🡒 Ordinal.zero (.bvar 0) 🡒 orderIso (.bvar 1) (.bvar 0)) := by
  simp only [zeroIsoClosed,closeParameters,closeParameter,zeroIsoOpen,
    Semiformula.rewAux,Semiformula.imp_eq,Semiformula.neg_eq,coherenceRewNeg,
    Ordinal.zero_rew,orderIso_rew]
  finishSourceSyntax

theorem zeroIso_closed : zeroIsoClosed.freeVariables=∅ := by
  apply Semiformula.freeVariables_eq_empty_of_shift_eq
  rw [zeroIsoClosed_eq]
  change Semiformula.rewAux Rew.shift _ = _
  simp only [Semiformula.rewAux,Semiformula.imp_eq,Semiformula.neg_eq,coherenceRewNeg,
    Ordinal.zero_rew,orderIso_rew]
  finishSourceSyntax
#print axioms zeroIsoDerivation
#print axioms zeroIsoClosed_eq
#print axioms zeroIso_closed
end M6.PA.RelationalClosedCertificate
