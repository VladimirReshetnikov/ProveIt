import PA194LeastExcludesClosedTemplate
namespace PA194GreatestSuccessorClosedTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal
open PA194LeastExcludesClosedTemplate

def greatestSuccessorOpen : Form :=
  sourceImply (domain (.fvar 1)) (sourceImply (greatest (.fvar 1) (.fvar 0)) (successor (.fvar 0) (.fvar 1)))

def greatestSuccessorOpenProof : ND.Proof equalityContext greatestSuccessorOpen := by
  apply impIntro
  apply impIntro
  let Γ : List Form := greatest (.fvar 1) (.fvar 0) :: domain (.fvar 1) :: equalityContext
  let e : EqualityProofs Γ := ⟨assumption (by simp [Γ,equalityContext]),
    assumption (by simp [Γ,equalityContext]), assumption (by simp [Γ,equalityContext])⟩
  have hd : ND.Proof Γ (domain (.fvar 1)) := assumption (by simp [Γ])
  exact greatestSuccessor e 1 0 (andLeft (andLeft hd)) (assumption (by simp [Γ]))

def greatestSuccessorOpenDerivation : LO.FirstOrder.Derivation
    (equalityContext.map Semiformula.neg ++ [greatestSuccessorOpen]) :=
  (greatestSuccessorOpenProof).contra (by simp [ND.Proof])

def greatestSuccessorBound : Semiproposition M6.PA.RelationalSource.language 2 :=
  sourceImply (domain (.bvar 1)) (sourceImply (greatest (.bvar 1) (.bvar 0)) (successor (.bvar 0) (.bvar 1)))

theorem greatestSuccessorOpen_fvSup : greatestSuccessorOpen.fvSup = 2 := by decide

theorem greatestSuccessor_closure : greatestSuccessorOpen.univCl = ∀⁰ ∀⁰ greatestSuccessorBound := by
  simp only [Semiformula.coe_univCl_eq_univCl']
  unfold Semiformula.univCl'
  rw [greatestSuccessorOpen_fvSup]
  simp only [allClosure_succ, allClosure_zero, Rew.fixitr_succ, Rew.fixitr_zero, Rew.comp_id]
  change ∀⁰ ∀⁰ Semiformula.rewAux (Rew.fix.comp Rew.fix) greatestSuccessorOpen = _
  simp only [greatestSuccessorOpen,greatestSuccessorBound,sourceImply]
  ordinalSyntax

#print axioms greatestSuccessorOpenProof
#print axioms greatestSuccessorOpenDerivation
#print axioms greatestSuccessorOpen_fvSup
#print axioms greatestSuccessor_closure
end PA194GreatestSuccessorClosedTemplate
