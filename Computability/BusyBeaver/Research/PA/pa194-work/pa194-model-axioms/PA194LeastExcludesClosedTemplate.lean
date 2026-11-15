import PA194FoundationOrdinalInductionMinimal
import PA194OrdinalStepQuote
namespace PA194LeastExcludesClosedTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

def equalityContext : List Form := [reflexivityFormula,symmetryFormula,congruenceFormula]

def leastExcludesOpen : Form :=
  sourceImply (domain (.fvar 1)) (sourceImply (least (.fvar 2) (.fvar 1))
    (sourceImply (mem (.fvar 1) (.fvar 0)) (∼mem (.fvar 2) (.fvar 0))))

def leastExcludesOpenProof : ND.Proof equalityContext leastExcludesOpen := by
  apply impIntro
  apply impIntro
  apply impIntro
  let Γ := mem (.fvar 1) (.fvar 0) :: least (.fvar 2) (.fvar 1) :: domain (.fvar 1) :: equalityContext
  let e : EqualityProofs Γ := ⟨assumption (by simp [Γ,equalityContext]),
    assumption (by simp [Γ,equalityContext]), assumption (by simp [Γ,equalityContext])⟩
  exact leastExcludesMember e 2 1 0 (assumption (by simp [Γ]))
    (assumption (by simp [Γ])) (assumption (by simp [Γ]))

def leastExcludesOpenDerivation : LO.FirstOrder.Derivation
    (equalityContext.map Semiformula.neg ++ [leastExcludesOpen]) :=
  (leastExcludesOpenProof).contra (by simp [ND.Proof])

def leastExcludesBound : Semiproposition M6.PA.RelationalSource.language 3 :=
  sourceImply (domain (.bvar 1)) (sourceImply (least (.bvar 2) (.bvar 1))
    (sourceImply (mem (.bvar 1) (.bvar 0)) (∼mem (.bvar 2) (.bvar 0))))

theorem leastExcludesOpen_fvSup : leastExcludesOpen.fvSup = 3 := by decide

theorem leastExcludes_closure : leastExcludesOpen.univCl = ∀⁰ ∀⁰ ∀⁰ leastExcludesBound := by
  simp only [Semiformula.coe_univCl_eq_univCl']
  unfold Semiformula.univCl'
  rw [leastExcludesOpen_fvSup]
  simp only [allClosure_succ, allClosure_zero, Rew.fixitr_succ, Rew.fixitr_zero, Rew.comp_id]
  change ∀⁰ ∀⁰ ∀⁰ Semiformula.rewAux ((Rew.fix.comp Rew.fix).comp Rew.fix) leastExcludesOpen = _
  simp only [leastExcludesOpen,leastExcludesBound,sourceImply]
  ordinalSyntax

#print axioms leastExcludesOpenProof
#print axioms leastExcludesOpenDerivation
#print axioms leastExcludesOpen_fvSup
#print axioms leastExcludes_closure
end PA194LeastExcludesClosedTemplate
