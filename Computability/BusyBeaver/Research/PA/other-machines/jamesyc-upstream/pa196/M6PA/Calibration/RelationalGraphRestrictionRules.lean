module
public import M6PA.Theory
public import M6PA.Calibration.RelationalGraphRestrictionEdges
@[expose] public section

namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def strictRestrictionShift {Γ : List Form} (top g h : Nat)
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar top) (.fvar g) (.fvar h))) :
    ND.Proof (shifted Γ) (strictGraphRestriction (.fvar (top+1)) (.fvar (g+1)) (.fvar (h+1))) := by
  convert shiftProof hr using 1 <;> restrictionSyntax

def strictRestrictionAt {Γ : List Form} (top g h x y : Nat)
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar top) (.fvar g) (.fvar h))) :
    ND.Proof Γ (sourceIff (edge (.fvar h) (.fvar x) (.fvar y))
      (edge (.fvar g) (.fvar x) (.fvar y) ⋏ mem (.fvar top) (.fvar x))) := by
  convert allElim _ (.fvar y) (allElim _ (.fvar x) hr) using 1 <;> restrictionSyntax

def strictCutCases {Γ : List Form} (top g h x y : Nat)
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar top) (.fvar g) (.fvar h)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y))) :
    ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y) ⋏ mem (.fvar top) (.fvar x)) :=
  mp he (andLeft (strictRestrictionAt top g h x y hr))

def strictCutIntro {Γ : List Form} (top g h x y : Nat)
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar top) (.fvar g) (.fvar h)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (hi : ND.Proof Γ (mem (.fvar top) (.fvar x))) :
    ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y)) :=
  mp (andIntro he hi) (andRight (strictRestrictionAt top g h x y hr))

#print axioms strictRestrictionShift
#print axioms strictRestrictionAt
#print axioms strictCutCases
#print axioms strictCutIntro
end M6.PA.RelationalSource.PairGraph
