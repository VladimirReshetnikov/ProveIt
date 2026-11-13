module
public import M6PA.Theory
public import M6PA.Calibration.RelationalGraphRestrictionInclusiveEdges
@[expose] public section

namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def graphRestrictionShift {Γ : List Form} (top g h : Nat)
    (hr : ND.Proof Γ (graphRestriction (.fvar top) (.fvar g) (.fvar h))) :
    ND.Proof (shifted Γ) (graphRestriction (.fvar (top+1)) (.fvar (g+1)) (.fvar (h+1))) := by
  convert shiftProof hr using 1 <;> inclusiveRestrictionSyntax

def graphRestrictionAt {Γ : List Form} (top g h x y : Nat)
    (hr : ND.Proof Γ (graphRestriction (.fvar top) (.fvar g) (.fvar h))) :
    ND.Proof Γ (sourceIff (edge (.fvar h) (.fvar x) (.fvar y))
      (edge (.fvar g) (.fvar x) (.fvar y) ⋏ inclusiveDomain (.fvar top) (.fvar x))) := by
  convert allElim _ (.fvar y) (allElim _ (.fvar x) hr) using 1 <;> inclusiveRestrictionSyntax

def restrictionCases {Γ : List Form} (top g h x y : Nat)
    (hr : ND.Proof Γ (graphRestriction (.fvar top) (.fvar g) (.fvar h)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y))) :
    ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y) ⋏ inclusiveDomain (.fvar top) (.fvar x)) :=
  mp he (andLeft (graphRestrictionAt top g h x y hr))

def restrictionIntro {Γ : List Form} (top g h x y : Nat)
    (hr : ND.Proof Γ (graphRestriction (.fvar top) (.fvar g) (.fvar h)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (hi : ND.Proof Γ (inclusiveDomain (.fvar top) (.fvar x))) :
    ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y)) :=
  mp (andIntro he hi) (andRight (graphRestrictionAt top g h x y hr))

def graphRestrictionExists (top g : Ordinal.Term n) : Ordinal.Formula n :=
  ∃¹ graphRestriction (Rew.bShift top) (Rew.bShift g) (.bvar 0)

def graphRestrictionWitness {Γ : List Form} (e : Ordinal.EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (top g : Nat)
    (hs : ND.Proof Γ (separationFormula (domainEntryProperty (.fvar top)))) :
    ND.Proof Γ (graphRestrictionExists (.fvar top) (.fvar g)) := by
  apply exsElim (inclusiveCutExists top g hs)
  let σ : Ordinal.Formula 1 := inclusiveGraphCut (.fvar top) (.fvar g) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hc : ND.Proof C (inclusiveGraphCut (.fvar (top+1)) (.fvar (g+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> inclusiveRestrictionSyntax)
  have hr := inclusiveCutEdges (e.shift.up σ.free) (up (Ordinal.equalityTransShift et) σ.free)
    (top+1) (g+1) 0 hc
  have out : ND.Proof C (graphRestrictionExists (.fvar (top+1)) (.fvar (g+1))) := by
    apply exsIntro _ (.fvar 0)
    convert hr using 1 <;> (dsimp [graphRestrictionExists] <;> inclusiveRestrictionSyntax)
  convert out using 1 <;> (dsimp [C,σ,graphRestrictionExists] <;> inclusiveRestrictionSyntax)

#print axioms graphRestrictionWitness
#print axioms graphRestrictionShift
#print axioms graphRestrictionAt
#print axioms restrictionCases
#print axioms restrictionIntro
end M6.PA.RelationalSource.PairGraph
