module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionBijectionRules
@[expose] public section

/-! Universal typing, uniqueness and order of the actual composition graph. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def compositionTyped {Γ : List Form} (g h a b c k : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hu : ND.Proof Γ (graphTyped (.fvar h) (.fvar b) (.fvar c)))
    (hc : ND.Proof Γ (compositionCorrect (.fvar g) (.fvar h) (.fvar a) (.fvar k))) :
    ND.Proof Γ (graphTyped (.fvar k) (.fvar a) (.fvar c)) := by
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (k+1+1)) (.fvar 1) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted (Γ))) d := assumption (by simp)
  have tt : ND.Proof (d :: shifted (shifted (Γ))) (graphTyped (.fvar (g+1+1)) (.fvar (a+1+1)) (.fvar (b+1+1))) := by
    convert up (shiftProof (shiftProof (ht))) d using 1 <;> compositionSyntax
  have uu : ND.Proof (d :: shifted (shifted (Γ))) (graphTyped (.fvar (h+1+1)) (.fvar (b+1+1)) (.fvar (c+1+1))) := by
    convert up (shiftProof (shiftProof (hu))) d using 1 <;> compositionSyntax
  have cc : ND.Proof (d :: shifted (shifted (Γ)))
      (compositionCorrect (.fvar (g+1+1)) (.fvar (h+1+1)) (.fvar (a+1+1)) (.fvar (k+1+1))) := by
    convert up (shiftProof (shiftProof (hc))) d using 1 <;> compositionSyntax
  have out := compositionTypedAt (g+1+1) (h+1+1) (a+1+1) (b+1+1) (c+1+1) (k+1+1) 1 0 tt uu cc hd
  convert impIntro out using 1 <;> (dsimp [d] <;> compositionSyntax)

def compositionFunctional {Γ : List Form} (E : FormulaEquality Γ) (g h a k : Nat)
    (ht : ND.Proof Γ (graphFunctional (.fvar g)))
    (hu : ND.Proof Γ (graphFunctional (.fvar h)))
    (hc : ND.Proof Γ (compositionCorrect (.fvar g) (.fvar h) (.fvar a) (.fvar k))) :
    ND.Proof Γ (graphFunctional (.fvar k)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (k+1+1+1)) (.fvar 2) (.fvar 1) ⋏ edge (.fvar (k+1+1+1)) (.fvar 2) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted (shifted (Γ)))) d := assumption (by simp)
  have tt : ND.Proof (d :: shifted (shifted (shifted (Γ)))) (graphFunctional (.fvar (g+1+1+1))) := by
    convert up (shiftProof (shiftProof (shiftProof (ht)))) d using 1 <;> compositionSyntax
  have uu : ND.Proof (d :: shifted (shifted (shifted (Γ)))) (graphFunctional (.fvar (h+1+1+1))) := by
    convert up (shiftProof (shiftProof (shiftProof (hu)))) d using 1 <;> compositionSyntax
  have cc : ND.Proof (d :: shifted (shifted (shifted (Γ))))
      (compositionCorrect (.fvar (g+1+1+1)) (.fvar (h+1+1+1)) (.fvar (a+1+1+1)) (.fvar (k+1+1+1))) := by
    convert up (shiftProof (shiftProof (shiftProof (hc)))) d using 1 <;> compositionSyntax
  have ee := E.shifted.shifted.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have out := compositionFunctionalAt ee (g+1+1+1) (h+1+1+1) (a+1+1+1) (k+1+1+1) 2 1 0 tt uu cc (andLeft hd) (andRight hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> compositionSyntax)

def compositionInjective {Γ : List Form} (E : FormulaEquality Γ) (g h a k : Nat)
    (ht : ND.Proof Γ (graphInjective (.fvar g)))
    (hu : ND.Proof Γ (graphInjective (.fvar h)))
    (hc : ND.Proof Γ (compositionCorrect (.fvar g) (.fvar h) (.fvar a) (.fvar k))) :
    ND.Proof Γ (graphInjective (.fvar k)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (k+1+1+1)) (.fvar 2) (.fvar 0) ⋏ edge (.fvar (k+1+1+1)) (.fvar 1) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted (shifted (Γ)))) d := assumption (by simp)
  have tt : ND.Proof (d :: shifted (shifted (shifted (Γ)))) (graphInjective (.fvar (g+1+1+1))) := by
    convert up (shiftProof (shiftProof (shiftProof (ht)))) d using 1 <;> compositionSyntax
  have uu : ND.Proof (d :: shifted (shifted (shifted (Γ)))) (graphInjective (.fvar (h+1+1+1))) := by
    convert up (shiftProof (shiftProof (shiftProof (hu)))) d using 1 <;> compositionSyntax
  have cc : ND.Proof (d :: shifted (shifted (shifted (Γ))))
      (compositionCorrect (.fvar (g+1+1+1)) (.fvar (h+1+1+1)) (.fvar (a+1+1+1)) (.fvar (k+1+1+1))) := by
    convert up (shiftProof (shiftProof (shiftProof (hc)))) d using 1 <;> compositionSyntax
  have ee := E.shifted.shifted.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have out := compositionInjectiveAt ee (g+1+1+1) (h+1+1+1) (a+1+1+1) (k+1+1+1) 2 1 0 tt uu cc (andLeft hd) (andRight hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> compositionSyntax)

def compositionOrder {Γ : List Form} (g h a k : Nat)
    (ht : ND.Proof Γ (graphOrder (.fvar g)))
    (hu : ND.Proof Γ (graphOrder (.fvar h)))
    (hc : ND.Proof Γ (compositionCorrect (.fvar g) (.fvar h) (.fvar a) (.fvar k))) :
    ND.Proof Γ (graphOrder (.fvar k)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (k+1+1+1+1)) (.fvar 3) (.fvar 1) ⋏ edge (.fvar (k+1+1+1+1)) (.fvar 2) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted (shifted (shifted (Γ))))) d := assumption (by simp)
  have tt : ND.Proof (d :: shifted (shifted (shifted (shifted (Γ))))) (graphOrder (.fvar (g+1+1+1+1))) := by
    convert up (shiftProof (shiftProof (shiftProof (shiftProof (ht))))) d using 1 <;> compositionSyntax
  have uu : ND.Proof (d :: shifted (shifted (shifted (shifted (Γ))))) (graphOrder (.fvar (h+1+1+1+1))) := by
    convert up (shiftProof (shiftProof (shiftProof (shiftProof (hu))))) d using 1 <;> compositionSyntax
  have cc : ND.Proof (d :: shifted (shifted (shifted (shifted (Γ)))))
      (compositionCorrect (.fvar (g+1+1+1+1)) (.fvar (h+1+1+1+1)) (.fvar (a+1+1+1+1)) (.fvar (k+1+1+1+1))) := by
    convert up (shiftProof (shiftProof (shiftProof (shiftProof (hc))))) d using 1 <;> compositionSyntax
  have out := compositionOrderAt (g+1+1+1+1) (h+1+1+1+1) (a+1+1+1+1) (k+1+1+1+1) 3 2 1 0 tt uu cc (andLeft hd) (andRight hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> compositionSyntax)

#print axioms compositionTyped
#print axioms compositionFunctional
#print axioms compositionInjective
#print axioms compositionOrder
end M6.PA.RelationalSource.PairGraph
