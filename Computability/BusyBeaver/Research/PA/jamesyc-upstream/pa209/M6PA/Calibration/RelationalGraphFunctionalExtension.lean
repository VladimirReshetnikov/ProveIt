module
public import M6PA.Theory
public import M6PA.Calibration.RelationalGraphFreshInput
@[expose] public section

/-! Functionality of an exact graph extension at a fresh input. Freshness is
an explicit syntactic no-output proof, discharged for ordinal successors next. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def oldEdgeClash {Γ : List Form} (E : FormulaEquality Γ) (g a x y : Nat)
    (hn : ND.Proof Γ (hasOutput (.fvar g) (.fvar a)).neg)
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (hxa : ND.Proof Γ (eq (.fvar x) (.fvar a))) : ND.Proof Γ ⊥ :=
  contradiction (outputIntro g a y (edgeInputTransport E g x a y hxa he)) hn

def functionalExtensionAt {Γ : List Form} (E : FormulaEquality Γ) (g h a b x y z : Nat)
    (hf : ND.Proof Γ (graphFunctional (.fvar g)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)))
    (hn : ND.Proof Γ (hasOutput (.fvar g) (.fvar a)).neg)
    (hy : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y)))
    (hz : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar z))) :
    ND.Proof Γ (eq (.fvar y) (.fvar z)) := by
  have cy := mp hy (andLeft (exactAt g h a b x y hx))
  have cz := mp hz (andLeft (exactAt g h a b x z hx))
  apply orElim cy
  · let q : Form := edge (.fvar g) (.fvar x) (.fvar y)
    apply orElim (up cz q)
    · exact graphFunctionalAt g x y z (up (up hf q) _) (assumption (by simp [q])) (assumption (by simp))
    · let r : Form := eq (.fvar x) (.fvar a) ⋏ eq (.fvar z) (.fvar b)
      have hp : ND.Proof (r::q::Γ) r := assumption (by simp)
      let EE := E.weaken (fun t ht => List.mem_cons_of_mem r (List.mem_cons_of_mem q ht))
      exact botElim (oldEdgeClash EE g a x y (up (up hn q) r)
        (assumption (by simp [q])) (andLeft hp))
  · let q : Form := eq (.fvar x) (.fvar a) ⋏ eq (.fvar y) (.fvar b)
    apply orElim (up cz q)
    · let r : Form := edge (.fvar g) (.fvar x) (.fvar z)
      have hp : ND.Proof (r::q::Γ) q := assumption (by simp)
      let EE := E.weaken (fun t ht => List.mem_cons_of_mem r (List.mem_cons_of_mem q ht))
      exact botElim (oldEdgeClash EE g a x z (up (up hn q) r)
        (assumption (by simp)) (andLeft hp))
    · let r : Form := eq (.fvar x) (.fvar a) ⋏ eq (.fvar z) (.fvar b)
      have hq : ND.Proof (r::q::Γ) q := assumption (by simp)
      have hr : ND.Proof (r::q::Γ) r := assumption (by simp)
      let EE := E.weaken (fun t ht => List.mem_cons_of_mem r (List.mem_cons_of_mem q ht))
      exact EE.transitivityOf (andRight hq) (EE.symmetryOf (andRight hr))

def functionalExtension {Γ : List Form} (E : FormulaEquality Γ) (g h a b : Nat)
    (hf : ND.Proof Γ (graphFunctional (.fvar g)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)))
    (hn : ND.Proof Γ (hasOutput (.fvar g) (.fvar a)).neg) :
    ND.Proof Γ (graphFunctional (.fvar h)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  have ff := graphFunctionalShift (g+1+1) (graphFunctionalShift (g+1) (graphFunctionalShift g hf))
  have xx := exactShift (g+1+1) (h+1+1) (a+1+1) (b+1+1)
    (exactShift (g+1) (h+1) (a+1) (b+1) (exactShift g h a b hx))
  have nn := noOutputShift (g+1+1) (a+1+1) (noOutputShift (g+1) (a+1) (noOutputShift g a hn))
  have result : ND.Proof (shifted (shifted (shifted Γ)))
      (sourceImply (edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏
        edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 0)) (eq (.fvar 1) (.fvar 0))) := by
    apply impIntro
    let q : Form := edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏
      edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 0)
    have hp : ND.Proof (q::shifted (shifted (shifted Γ))) q := assumption (by simp)
    let EE := E.shifted.shifted.shifted.weaken (fun r hr => List.mem_cons_of_mem q hr)
    exact functionalExtensionAt EE (g+1+1+1) (h+1+1+1) (a+1+1+1) (b+1+1+1) 2 1 0
      (up ff q) (up xx q) (up nn q) (andLeft hp) (andRight hp)
  convert result using 1 ; traceSyntax

def successorFunctional {Γ : List Form} (E : FormulaEquality Γ) (top a b g h : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar top)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar a)))
    (hd : ND.Proof Γ (graphDomain (.fvar top) (.fvar g)))
    (hf : ND.Proof Γ (graphFunctional (.fvar g)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b))) :
    ND.Proof Γ (graphFunctional (.fvar h)) :=
  functionalExtension E g h a b hf hx (noOutputSuccessor E.core top a g ht hs hd)

#print axioms functionalExtensionAt
#print axioms functionalExtension
#print axioms successorFunctional
end M6.PA.RelationalSource.PairGraph
