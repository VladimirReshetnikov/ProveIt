module
public import M6PA.Theory
public import M6PA.Calibration.RelationalGraphRestrictionInclusiveRules
public import M6PA.Calibration.RelationalGraphOperations
@[expose] public section

namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def restrictionOutputInside {Γ : List Form} (top g h x : Nat)
    (hr : ND.Proof Γ (graphRestriction (.fvar top) (.fvar g) (.fvar h)))
    (ho : ND.Proof Γ (hasOutput (.fvar h) (.fvar x))) :
    ND.Proof Γ (inclusiveDomain (.fvar top) (.fvar x)) := by
  apply exsElim ho
  let σ : Ordinal.Formula 1 := edge (.fvar h) (.fvar x) (.bvar 0)
  let C := σ.free :: shifted Γ
  have he : ND.Proof C (edge (.fvar (h+1)) (.fvar (x+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> inclusiveRestrictionSyntax)
  have out := andRight (restrictionCases (top+1) (g+1) (h+1) (x+1) 0
    (up (graphRestrictionShift top g h hr) σ.free) he)
  convert out using 1 <;> (dsimp [C,σ] <;> inclusiveRestrictionSyntax)

def restrictionOutputIntro {Γ : List Form} (top g h x : Nat)
    (hr : ND.Proof Γ (graphRestriction (.fvar top) (.fvar g) (.fvar h)))
    (ho : ND.Proof Γ (hasOutput (.fvar g) (.fvar x)))
    (hi : ND.Proof Γ (inclusiveDomain (.fvar top) (.fvar x))) :
    ND.Proof Γ (hasOutput (.fvar h) (.fvar x)) := by
  apply exsElim ho
  let σ : Ordinal.Formula 1 := edge (.fvar g) (.fvar x) (.bvar 0)
  let C := σ.free :: shifted Γ
  have he : ND.Proof C (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> inclusiveRestrictionSyntax)
  have ii : ND.Proof C (inclusiveDomain (.fvar (top+1)) (.fvar (x+1))) := by
    convert up (shiftProof hi) σ.free using 1 <;> inclusiveRestrictionSyntax
  have out := outputIntro (h+1) (x+1) 0 (restrictionIntro (top+1) (g+1) (h+1) (x+1) 0
    (up (graphRestrictionShift top g h hr) σ.free) he ii)
  convert out using 1 <;> (dsimp [C,σ,hasOutput] <;> inclusiveRestrictionSyntax)

def restrictionDomainAt {Γ : List Form} (top next g h x : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar next)))
    (hd : ND.Proof Γ (graphDomain (.fvar next) (.fvar g)))
    (hr : ND.Proof Γ (graphRestriction (.fvar top) (.fvar g) (.fvar h))) :
    ND.Proof Γ (sourceIff (hasOutput (.fvar h) (.fvar x))
      (inclusiveDomain (.fvar top) (.fvar x))) := by
  apply andIntro
  · apply impIntro
    exact restrictionOutputInside top g h x (up hr _) (assumption (by simp))
  · apply impIntro
    let premise : Form := inclusiveDomain (.fvar top) (.fvar x)
    have hi : ND.Proof (premise::Γ) premise := assumption (by simp)
    have hm := mp hi (up (andRight (Ordinal.successorAt top next x hs)) premise)
    have ho := mp (ND.orLeft hm) (up (andRight (graphDomainAt next g x hd)) premise)
    exact restrictionOutputIntro top g h x (up hr premise) ho hi

def restrictionDomain {Γ : List Form} (top next g h : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar next)))
    (hd : ND.Proof Γ (graphDomain (.fvar next) (.fvar g)))
    (hr : ND.Proof Γ (graphRestriction (.fvar top) (.fvar g) (.fvar h))) :
    ND.Proof Γ (graphDomain (.fvar top) (.fvar h)) := by
  apply allIntro
  have dd : ND.Proof (shifted Γ) (graphDomain (.fvar (next+1)) (.fvar (g+1))) := by
    convert shiftProof hd using 1 <;> inclusiveRestrictionSyntax
  have out := restrictionDomainAt (top+1) (next+1) (g+1) (h+1) 0
    (Ordinal.successorShift top next hs) dd (graphRestrictionShift top g h hr)
  convert out using 1 <;> (dsimp [hasOutput] <;> inclusiveRestrictionSyntax)

#print axioms restrictionOutputInside
#print axioms restrictionOutputIntro
#print axioms restrictionDomainAt
#print axioms restrictionDomain
end M6.PA.RelationalSource.PairGraph
