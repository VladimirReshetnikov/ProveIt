import PA194SourceEqualityIsoOpen
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSectionVars false
namespace PA194SourceEqualityIso
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
/-- The fixed reflexivity sentence is stable under shifting free variables. -/
def shiftRefl {Γ : List Form} (hr : ND.Proof Γ orderIsoReflexivityStatement) :
    ND.Proof (ND.shifted Γ) orderIsoReflexivityStatement := by
  have h := ND.shiftProof hr
  convert h using 1 <;> (simp only [orderIsoReflexivityStatement] <;> isoSyntax)

def eqIsoClosed : Form := ∀⁰ ∀⁰ ∀⁰
  (Ordinal.domain (.bvar 1) 🡒 Ordinal.domain (.bvar 0) 🡒
    eq (.bvar 1) (.bvar 2) 🡒 eq (.bvar 0) (.bvar 2) 🡒 orderIso (.bvar 1) (.bvar 0))

def eqIsoClosedProof {Γ : List Form} (E : FormulaEquality Γ)
    (hr : ND.Proof Γ orderIsoReflexivityStatement) : ND.Proof Γ eqIsoClosed := by
  unfold eqIsoClosed
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  have h := eqIsoAt E.shifted.shifted.shifted (shiftRefl (shiftRefl (shiftRefl hr))) 2 1 0
  convert h using 1 <;>
    simp only [Semiformula.free,Rewriting.free,Semiformula.rewAux,domain_rew,orderIso_rew,eq,Rew.free,Rew.q,Rew.func]
  all_goals simp [← Semiformula.neg_eq,Semiformula.rewAux_neg,domain_rew,orderIso_rew,eq,Rew.free,Rew.q,Rew.func]
  all_goals simp [Semiformula.rewAux,Rew.free,Rew.q,Rew.func,Function.comp_def]
  all_goals congr 4
  all_goals try (change (Semiformula.nrel (L := language) Relation.eq _ : Form) = Semiformula.nrel (L := language) Relation.eq _; congr 1)
  all_goals funext i
  all_goals fin_cases i <;> rfl

#print axioms shiftRefl
#print axioms eqIsoClosedProof
end PA194SourceEqualityIso
