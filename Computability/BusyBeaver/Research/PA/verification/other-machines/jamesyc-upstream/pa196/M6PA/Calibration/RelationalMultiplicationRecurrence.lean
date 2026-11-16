module
public import M6PA.Theory
public import M6PA.Calibration.RelationalGraphRangeExtension
public import M6PA.Calibration.RelationalGraphFunctionalExtension
public import M6PA.Calibration.RelationalMultiplicationTrace
@[expose] public section

/-! Finite recurrence elimination and transport for multiplication graphs. Existential previous outputs are real graph members. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
set_option maxHeartbeats 600000
attribute [local irreducible] addResult addPrefix mulPrefix
open Ordinal (Term Formula)

def mulPrevious (g base x y : Term n) : Formula n :=
  ∃¹ (edge (Rew.bShift g) (Rew.bShift x) (.bvar 0) ⋏ addResult (.bvar 0) (Rew.bShift base) (Rew.bShift y))

macro "mulPreviousSyntax" : tactic => `(tactic| (first | (simp only [mulPrevious]; mulSyntax) | mulSyntax))

def mulRecurrenceAt {Γ : List Form} (g base x y z : Nat)
    (hr : ND.Proof Γ (mulRecurrence (.fvar g) (.fvar base)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar z) (.fvar x))) :
    ND.Proof Γ (mulPrevious (.fvar g) (.fvar base) (.fvar z) (.fvar y)) := by
  have hi : ND.Proof Γ (sourceImply (edge (.fvar g) (.fvar x) (.fvar y) ⋏
      Ordinal.successor (.fvar z) (.fvar x)) (mulPrevious (.fvar g) (.fvar base) (.fvar z) (.fvar y))) := by
    convert allElim _ (.fvar z) (allElim _ (.fvar y) (allElim _ (.fvar x) hr)) using 1
    mulPreviousSyntax
  exact mp (andIntro he hs) hi

#print axioms mulRecurrenceAt

end M6.PA.RelationalSource.PairGraph
