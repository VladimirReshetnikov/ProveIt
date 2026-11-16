import PA194FoundationTraceGraph
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def pointShift {Γ : List Form} (a b g : Nat)
    (h : ND.Proof Γ (pointGraph (.fvar a) (.fvar b) (.fvar g))) :
    ND.Proof (shifted Γ) (pointGraph (.fvar (a+1)) (.fvar (b+1)) (.fvar (g+1))) := by
  convert shiftProof h using 1 ; traceSyntax

def exactShift {Γ : List Form} (g h a b : Nat)
    (d : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b))) :
    ND.Proof (shifted Γ) (exactExtension (.fvar (g+1)) (.fvar (h+1)) (.fvar (a+1)) (.fvar (b+1))) := by
  convert shiftProof d using 1 ; simp only [exactExtension,classified] ; graphSyntax

def exactAt {Γ : List Form} (g h a b x y : Nat)
    (d : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b))) :
    ND.Proof Γ (sourceIff (edge (.fvar h) (.fvar x) (.fvar y))
      (classified (.fvar g) (.fvar a) (.fvar b) (.fvar x) (.fvar y))) := by
  convert allElim _ (.fvar y) (allElim _ (.fvar x) d) using 1
  simp only [exactExtension,classified]; graphSyntax

def pointFromExact {Γ : List Form} (g h a b : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar g)))
    (he : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b))) :
    ND.Proof Γ (pointGraph (.fvar a) (.fvar b) (.fvar h)) := by
  apply allIntro
  apply allIntro
  have zz := Ordinal.zeroShift (g+1) (Ordinal.zeroShift g hz)
  have ex := exactAt (g+1+1) (h+1+1) (a+1+1) (b+1+1) 1 0
    (exactShift (g+1) (h+1) (a+1) (b+1) (exactShift g h a b he))
  have result : ND.Proof (shifted (shifted Γ))
      (sourceIff (edge (.fvar (h+1+1)) (.fvar 1) (.fvar 0))
        (eq (.fvar 1) (.fvar (a+1+1)) ⋏ eq (.fvar 0) (.fvar (b+1+1)))) := by
    apply andIntro
    · apply impIntro
      have hh := mp (assumption (by simp)) (up (andLeft ex) (edge (.fvar (h+1+1)) (.fvar 1) (.fvar 0)))
      apply orElim hh
      · exact botElim (emptyNoEdge (g+1+1) 1 0 (up (up zz _) _) (assumption (by simp)))
      · exact assumption (by simp)
    · apply impIntro
      exact mp (ND.orRight (assumption (by simp))) (up (andRight ex) _)
  convert result using 1 ; traceSyntax

def pointFunctional {Γ : List Form} (E : FormulaEquality Γ) (a b g : Nat)
    (h : ND.Proof Γ (pointGraph (.fvar a) (.fvar b) (.fvar g))) :
    ND.Proof Γ (graphFunctional (.fvar g)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  have hh := pointShift (a+1+1) (b+1+1) (g+1+1)
    (pointShift (a+1) (b+1) (g+1) (pointShift a b g h))
  have hy := andLeft (pointAt (a+1+1+1) (b+1+1+1) (g+1+1+1) 2 1 hh)
  have hz := andLeft (pointAt (a+1+1+1) (b+1+1+1) (g+1+1+1) 2 0 hh)
  have result : ND.Proof (shifted (shifted (shifted Γ)))
      (sourceImply (edge (.fvar (g+1+1+1)) (.fvar 2) (.fvar 1) ⋏
        edge (.fvar (g+1+1+1)) (.fvar 2) (.fvar 0)) (eq (.fvar 1) (.fvar 0))) := by
    apply impIntro
    let q : Form := edge (.fvar (g+1+1+1)) (.fvar 2) (.fvar 1) ⋏ edge (.fvar (g+1+1+1)) (.fvar 2) (.fvar 0)
    have hp : ND.Proof (q :: shifted (shifted (shifted Γ))) q := assumption (by simp)
    let EE := E.shifted.shifted.shifted.weaken (fun r hr => List.mem_cons_of_mem q hr)
    exact EE.transitivityOf (andRight (mp (andLeft hp) (up hy q)))
      (EE.symmetryOf (andRight (mp (andRight hp) (up hz q))))
  convert result using 1 ; traceSyntax

def domainShift {Γ : List Form} (b : Nat) (hb : ND.Proof Γ (Ordinal.domain (.fvar b))) :
    ND.Proof (shifted Γ) (Ordinal.domain (.fvar (b+1))) := by
  convert shiftProof hb using 1 ; ordinalSyntax

def pointRange {Γ : List Form} (E : FormulaEquality Γ) (a b g : Nat)
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (h : ND.Proof Γ (pointGraph (.fvar a) (.fvar b) (.fvar g))) :
    ND.Proof Γ (graphRange (.fvar g)) := by
  apply allIntro
  apply allIntro
  have hp := pointShift (a+1) (b+1) (g+1) (pointShift a b g h)
  have hh := domainShift (b+1) (domainShift b hb)
  have hi := andLeft (pointAt (a+1+1) (b+1+1) (g+1+1) 1 0 hp)
  have result : ND.Proof (shifted (shifted Γ))
      (sourceImply (edge (.fvar (g+1+1)) (.fvar 1) (.fvar 0)) (Ordinal.domain (.fvar 0))) := by
    apply impIntro
    let q : Form := edge (.fvar (g+1+1)) (.fvar 1) (.fvar 0)
    let EE := E.shifted.shifted.weaken (fun r hr => List.mem_cons_of_mem q hr)
    have he := andRight (mp (assumption (by simp [q])) (up hi q))
    exact domainTransport EE (b+1+1) 0 (EE.symmetryOf he) (up hh q)
  convert result using 1 ; traceSyntax

#print axioms pointFromExact
#print axioms pointFunctional
#print axioms pointRange
end M6.PA.RelationalSource.PairGraph

