import PA194FoundationOrdinalInductionUniform
import PA194LeastExcludesClosedTemplate
namespace PA194SuccessorMemberClosedTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal
open PA194LeastExcludesClosedTemplate

def successorMemberOpen : Form :=
  sourceImply (successor (.fvar 1) (.fvar 0)) (mem (.fvar 0) (.fvar 1))

def successorMemberOpenProof : ND.Proof equalityContext successorMemberOpen := by
  apply impIntro
  let Γ := successor (.fvar 1) (.fvar 0) :: equalityContext
  let e : EqualityProofs Γ := ⟨assumption (by simp [Γ,equalityContext]),
    assumption (by simp [Γ,equalityContext]), assumption (by simp [Γ,equalityContext])⟩
  have hs : ND.Proof Γ (successor (.fvar 1) (.fvar 0)) := assumption (by simp [Γ])
  exact mp (ND.orRight (eqRefl e 1)) (andRight (successorAt 1 0 1 hs))

def successorMemberOpenDerivation : LO.FirstOrder.Derivation
    (equalityContext.map Semiformula.neg ++ [successorMemberOpen]) :=
  successorMemberOpenProof.contra (by simp [ND.Proof])

def successorMemberBound : Semiproposition M6.PA.RelationalSource.language 2 :=
  sourceImply (successor (.bvar 1) (.bvar 0)) (mem (.bvar 0) (.bvar 1))

theorem successorMemberOpen_fvSup : successorMemberOpen.fvSup = 2 := by decide

theorem successorMember_closure : successorMemberOpen.univCl = ∀⁰ ∀⁰ successorMemberBound := by
  simp only [Semiformula.coe_univCl_eq_univCl']
  unfold Semiformula.univCl'
  rw [successorMemberOpen_fvSup]
  simp only [allClosure_succ, allClosure_zero, Rew.fixitr_succ, Rew.fixitr_zero, Rew.comp_id]
  change ∀⁰ ∀⁰ Semiformula.rewAux (Rew.fix.comp Rew.fix) successorMemberOpen = _
  simp only [successorMemberOpen,successorMemberBound,sourceImply]
  ordinalSyntax

#print axioms successorMemberOpenProof
#print axioms successorMemberOpenDerivation
#print axioms successorMemberOpen_fvSup
#print axioms successorMember_closure
end PA194SuccessorMemberClosedTemplate
