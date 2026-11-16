module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseBijectionRules
@[expose] public section

/-! Universal typing, uniqueness, and order laws for the reversed graph. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def inverseTyped {Γ : List Form} (g a b h : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hc : ND.Proof Γ (inverseCorrect (.fvar g) (.fvar a) (.fvar h))) :
    ND.Proof Γ (graphTyped (.fvar h) (.fvar b) (.fvar a)) := by
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (h+1+1)) (.fvar 1) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted (Γ))) d := assumption (by simp)
  have tt : ND.Proof (d :: shifted (shifted (Γ))) (graphTyped (.fvar (g+1+1)) (.fvar (a+1+1)) (.fvar (b+1+1))) := by
    have hh := up (shiftProof (shiftProof (ht))) d
    convert hh using 1 <;> inverseSyntax
  have cc : ND.Proof (d :: shifted (shifted (Γ)))
      (inverseCorrect (.fvar (g+1+1)) (.fvar (a+1+1)) (.fvar (h+1+1))) := by
    have hh := up (shiftProof (shiftProof (hc))) d
    convert hh using 1 <;> inverseSyntax
  have out := inverseTypedAt (g+1+1) (a+1+1) (b+1+1) (h+1+1) 1 0 tt cc hd
  convert impIntro out using 1 <;> (dsimp [d] <;> inverseSyntax)

def inverseFunctional {Γ : List Form} (g a h : Nat)
    (hi : ND.Proof Γ (graphInjective (.fvar g)))
    (hc : ND.Proof Γ (inverseCorrect (.fvar g) (.fvar a) (.fvar h))) :
    ND.Proof Γ (graphFunctional (.fvar h)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏ edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted (shifted (Γ)))) d := assumption (by simp)
  have tt : ND.Proof (d :: shifted (shifted (shifted (Γ)))) (graphInjective (.fvar (g+1+1+1))) := by
    have hh := up (shiftProof (shiftProof (shiftProof (hi)))) d
    convert hh using 1 <;> inverseSyntax
  have cc : ND.Proof (d :: shifted (shifted (shifted (Γ))))
      (inverseCorrect (.fvar (g+1+1+1)) (.fvar (a+1+1+1)) (.fvar (h+1+1+1))) := by
    have hh := up (shiftProof (shiftProof (shiftProof (hc)))) d
    convert hh using 1 <;> inverseSyntax
  have out := inverseFunctionalAt (g+1+1+1) (a+1+1+1) (h+1+1+1) 2 1 0 tt cc (andLeft hd) (andRight hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> inverseSyntax)

def inverseInjective {Γ : List Form} (g a h : Nat)
    (hf : ND.Proof Γ (graphFunctional (.fvar g)))
    (hc : ND.Proof Γ (inverseCorrect (.fvar g) (.fvar a) (.fvar h))) :
    ND.Proof Γ (graphInjective (.fvar h)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 0) ⋏ edge (.fvar (h+1+1+1)) (.fvar 1) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted (shifted (Γ)))) d := assumption (by simp)
  have tt : ND.Proof (d :: shifted (shifted (shifted (Γ)))) (graphFunctional (.fvar (g+1+1+1))) := by
    have hh := up (shiftProof (shiftProof (shiftProof (hf)))) d
    convert hh using 1 <;> inverseSyntax
  have cc : ND.Proof (d :: shifted (shifted (shifted (Γ))))
      (inverseCorrect (.fvar (g+1+1+1)) (.fvar (a+1+1+1)) (.fvar (h+1+1+1))) := by
    have hh := up (shiftProof (shiftProof (shiftProof (hc)))) d
    convert hh using 1 <;> inverseSyntax
  have out := inverseInjectiveAt (g+1+1+1) (a+1+1+1) (h+1+1+1) 2 1 0 tt cc (andLeft hd) (andRight hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> inverseSyntax)

def inverseOrder {Γ : List Form} (g a h : Nat)
    (ho : ND.Proof Γ (graphOrder (.fvar g)))
    (hc : ND.Proof Γ (inverseCorrect (.fvar g) (.fvar a) (.fvar h))) :
    ND.Proof Γ (graphOrder (.fvar h)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (h+1+1+1+1)) (.fvar 3) (.fvar 1) ⋏ edge (.fvar (h+1+1+1+1)) (.fvar 2) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted (shifted (shifted (Γ))))) d := assumption (by simp)
  have tt : ND.Proof (d :: shifted (shifted (shifted (shifted (Γ))))) (graphOrder (.fvar (g+1+1+1+1))) := by
    have hh := up (shiftProof (shiftProof (shiftProof (shiftProof (ho))))) d
    convert hh using 1 <;> inverseSyntax
  have cc : ND.Proof (d :: shifted (shifted (shifted (shifted (Γ)))))
      (inverseCorrect (.fvar (g+1+1+1+1)) (.fvar (a+1+1+1+1)) (.fvar (h+1+1+1+1))) := by
    have hh := up (shiftProof (shiftProof (shiftProof (shiftProof (hc))))) d
    convert hh using 1 <;> inverseSyntax
  have out := inverseOrderAt (g+1+1+1+1) (a+1+1+1+1) (h+1+1+1+1) 3 2 1 0 tt cc (andLeft hd) (andRight hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> inverseSyntax)

#print axioms inverseTyped
#print axioms inverseFunctional
#print axioms inverseInjective
#print axioms inverseOrder
end M6.PA.RelationalSource.PairGraph
