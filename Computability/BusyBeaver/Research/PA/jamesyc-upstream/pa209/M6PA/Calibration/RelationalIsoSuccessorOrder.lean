module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoSuccessorOrderRules
public import M6PA.Calibration.RelationalOrdinalInductionMembers
@[expose] public section

/-! Universal order clause of the exact successor extension. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def successorGraphOrder {Γ : List Form} (E : FormulaEquality Γ) (g h a b : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (ho : ND.Proof Γ (graphOrder (.fvar g)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b))) :
    ND.Proof Γ (graphOrder (.fvar h)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  apply allIntro
  let p : Form := edge (.fvar (h+1+1+1+1)) (.fvar 3) (.fvar 1) ⋏
    edge (.fvar (h+1+1+1+1)) (.fvar 2) (.fvar 0)
  have hp : ND.Proof (p::shifted (shifted (shifted (shifted Γ)))) p := assumption (by simp)
  let EE := E.shifted.shifted.shifted.shifted.weaken (fun q hq => List.mem_cons_of_mem p hq)
  have tt := (orderTypedShift (g+1+1+1) (a+1+1+1) (b+1+1+1) (orderTypedShift (g+1+1) (a+1+1) (b+1+1) (orderTypedShift (g+1) (a+1) (b+1) (orderTypedShift (g) (a) (b) ht))))
  have aa := (Ordinal.domainShift (a+1+1+1) (Ordinal.domainShift (a+1+1) (Ordinal.domainShift (a+1) (Ordinal.domainShift (a) ha))))
  have bb := (Ordinal.domainShift (b+1+1+1) (Ordinal.domainShift (b+1+1) (Ordinal.domainShift (b+1) (Ordinal.domainShift (b) hb))))
  have oo := (orderOrderShift (g+1+1+1) (orderOrderShift (g+1+1) (orderOrderShift (g+1) (orderOrderShift (g) ho))))
  have xx := (exactShift (g+1+1+1) (h+1+1+1) (a+1+1+1) (b+1+1+1) (exactShift (g+1+1) (h+1+1) (a+1+1) (b+1+1) (exactShift (g+1) (h+1) (a+1) (b+1) (exactShift (g) (h) (a) (b) hx))))
  have out := successorOrderAt EE (g+1+1+1+1) (h+1+1+1+1) (a+1+1+1+1) (b+1+1+1+1) 3 2 1 0
    (up tt p) (up aa p) (up bb p) (up oo p) (up xx p) (andLeft hp) (andRight hp)
  convert impIntro out using 1 <;> (dsimp [p] <;> isoSyntax)

#print axioms successorGraphOrder
end M6.PA.RelationalSource.PairGraph
