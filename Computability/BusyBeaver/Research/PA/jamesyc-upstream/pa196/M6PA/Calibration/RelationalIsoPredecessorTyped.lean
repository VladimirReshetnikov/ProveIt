module
public import M6PA.Theory
public import M6PA.Calibration.RelationalGraphRestrictionRules
public import M6PA.Calibration.RelationalIsoEntriesRetype
public import M6PA.Calibration.RelationalOrderIsoRelationRules
@[expose] public section

/-! A strict cut through a displayed endpoint edge is typed by the two
predecessor containers. Existing actual entries are explicitly retyped. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def predecessorTypedAt {Γ : List Form} (g h p q x y : Nat)
    (ho : ND.Proof Γ (graphOrder (.fvar g)))
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar p) (.fvar g) (.fvar h)))
    (hpq : ND.Proof Γ (edge (.fvar g) (.fvar p) (.fvar q)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y))) :
    ND.Proof Γ (mem (.fvar p) (.fvar x) ⋏ mem (.fvar q) (.fvar y)) := by
  have hc := strictCutCases p g h x y hr he
  have order := orderOrderAt g p x q y ho hpq (andLeft hc)
  exact andIntro (andRight hc) (mp (andRight hc) (andLeft order))

def predecessorGraphTyped {Γ : List Form} (g h p q : Nat)
    (ho : ND.Proof Γ (graphOrder (.fvar g)))
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar p) (.fvar g) (.fvar h)))
    (hpq : ND.Proof Γ (edge (.fvar g) (.fvar p) (.fvar q))) :
    ND.Proof Γ (graphTyped (.fvar h) (.fvar p) (.fvar q)) := by
  apply allIntro
  apply allIntro
  let premise : Form := edge (.fvar (h+1+1)) (.fvar 1) (.fvar 0)
  have ee : ND.Proof (premise::shifted (shifted Γ))
      (edge (.fvar (g+1+1)) (.fvar (p+1+1)) (.fvar (q+1+1))) := by
    have hh := up (shiftProof (shiftProof hpq)) premise
    convert hh using 1 <;> isoSyntax
  have out := predecessorTypedAt (g+1+1) (h+1+1) (p+1+1) (q+1+1) 1 0
    (up (orderOrderShift (g+1) (orderOrderShift g ho)) premise)
    (up (strictRestrictionShift (p+1) (g+1) (h+1) (strictRestrictionShift p g h hr)) premise)
    ee (assumption (by simp [premise]))
  convert impIntro out using 1 <;> (dsimp [premise] <;> isoSyntax)

def predecessorGraphEntries {Γ : List Form} (g h p q b : Nat)
    (ho : ND.Proof Γ (graphOrder (.fvar g)))
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar p) (.fvar g) (.fvar h)))
    (hpq : ND.Proof Γ (edge (.fvar g) (.fvar p) (.fvar q)))
    (he : ND.Proof Γ (graphEntries (.fvar h) (.fvar p) (.fvar b))) :
    ND.Proof Γ (graphEntries (.fvar h) (.fvar p) (.fvar q)) :=
  graphEntriesRetype h p b p q he (predecessorGraphTyped g h p q ho hr hpq)

#print axioms predecessorTypedAt
#print axioms predecessorGraphTyped
#print axioms predecessorGraphEntries
end M6.PA.RelationalSource.PairGraph
