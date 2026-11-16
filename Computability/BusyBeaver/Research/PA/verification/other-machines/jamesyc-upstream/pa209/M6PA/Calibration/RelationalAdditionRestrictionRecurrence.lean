module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRestrictionInside
public import M6PA.Calibration.RelationalAdditionRecurrenceExtension
@[expose] public section

namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def restrictPrevious {Γ : List Form} (t g h x y : Nat)
    (hr : ND.Proof Γ (graphRestriction (.fvar t) (.fvar g) (.fvar h)))
    (hi : ND.Proof Γ (inclusiveDomain (.fvar t) (.fvar x)))
    (hp : ND.Proof Γ (addPrevious (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (addPrevious (.fvar h) (.fvar x) (.fvar y)) := by
  apply exsElim hp
  let σ : Ordinal.Formula 1 := edge (.fvar g) (.fvar x) (.bvar 0) ⋏ Ordinal.successor (.bvar 0) (.fvar y)
  let C := σ.free :: shifted Γ
  have hc : ND.Proof C (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0) ⋏
      Ordinal.successor (.fvar 0) (.fvar (y+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 ; dsimp [σ]; previousSyntax
  have ii : ND.Proof C (inclusiveDomain (.fvar (t+1)) (.fvar (x+1))) := by
    convert up (shiftProof hi) σ.free using 1 <;> inclusiveRestrictionSyntax
  have he := restrictionIntro (t+1) (g+1) (h+1) (x+1) 0
    (up (graphRestrictionShift t g h hr) σ.free) (andLeft hc) ii
  have out := previousIntro (h+1) (x+1) (y+1) 0 he (andRight hc)
  convert out using 1 <;> (dsimp [C,σ] <;> previousSyntax)

def restrictionRecurrenceAt {Γ : List Form} (E : FormulaEquality Γ) (t g h i y j : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hr : ND.Proof Γ (graphRestriction (.fvar t) (.fvar g) (.fvar h)))
    (hc : ND.Proof Γ (addRecurrence (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar i) (.fvar y)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar j) (.fvar i))) :
    ND.Proof Γ (addPrevious (.fvar h) (.fvar j) (.fvar y)) := by
  have old := restrictionCases t g h i y hr he
  exact restrictPrevious t g h j y hr
    (restrictionPredecessorInside E t i j ht (andRight old) hs)
    (recurrenceAt g i y j hc (andLeft old) hs)

def restrictionRecurrence {Γ : List Form} (E : FormulaEquality Γ) (t g h : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hr : ND.Proof Γ (graphRestriction (.fvar t) (.fvar g) (.fvar h)))
    (hc : ND.Proof Γ (addRecurrence (.fvar g))) :
    ND.Proof Γ (addRecurrence (.fvar h)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  have tt := domainShift (t+1+1) (domainShift (t+1) (domainShift t ht))
  have rr := graphRestrictionShift (t+1+1) (g+1+1) (h+1+1)
    (graphRestrictionShift (t+1) (g+1) (h+1) (graphRestrictionShift t g h hr))
  have cc := recurrenceShift (g+1+1) (recurrenceShift (g+1) (recurrenceShift g hc))
  have result : ND.Proof (shifted (shifted (shifted Γ)))
      (sourceImply (edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏ Ordinal.successor (.fvar 0) (.fvar 2))
        (addPrevious (.fvar (h+1+1+1)) (.fvar 0) (.fvar 1))) := by
    apply impIntro
    let q : Form := edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏ Ordinal.successor (.fvar 0) (.fvar 2)
    have hp : ND.Proof (q::shifted (shifted (shifted Γ))) q := assumption (by simp)
    let inc := fun p (hp : p ∈ shifted (shifted (shifted Γ))) => List.mem_cons_of_mem q hp
    exact restrictionRecurrenceAt (E.shifted.shifted.shifted.weaken inc)
      (t+1+1+1) (g+1+1+1) (h+1+1+1) 2 1 0
      (up tt q) (up rr q) (up cc q) (andLeft hp) (andRight hp)
  convert result using 1 ; previousSyntax

#print axioms restrictPrevious
#print axioms restrictionRecurrenceAt
#print axioms restrictionRecurrence
end M6.PA.RelationalSource.PairGraph
