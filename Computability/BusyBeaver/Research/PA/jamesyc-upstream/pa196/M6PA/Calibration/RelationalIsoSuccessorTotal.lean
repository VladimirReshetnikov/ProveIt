module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoSuccessorTotalRules
@[expose] public section

/-! Both universal totality clauses with their actual existential witnesses. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def successorGraphLeftTotal {Γ : List Form} (E : FormulaEquality Γ) (g h a b c : Nat)
    (hg : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar c)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b))) :
    ND.Proof Γ (graphLeftTotal (.fvar h) (.fvar c)) := by
  apply allIntro
  let premise : Form := mem (.fvar (c+1)) (.fvar 0)
  let EE := E.shifted.weaken (fun q hq => List.mem_cons_of_mem premise hq)
  have out := successorLeftAt EE (g+1) (h+1) (a+1) (b+1) (c+1) 0
    (up (orderLeftShift g a hg) premise)
    (up (Ordinal.successorShift a c hs) premise)
    (up (exactShift g h a b hx) premise) (assumption (by simp [premise]))
  convert impIntro out using 1 <;> (dsimp [premise,hasOutput] <;> isoSyntax)

def successorGraphRightTotal {Γ : List Form} (E : FormulaEquality Γ) (g h a b c : Nat)
    (hg : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar b) (.fvar c)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b))) :
    ND.Proof Γ (graphRightTotal (.fvar h) (.fvar c)) := by
  apply allIntro
  let premise : Form := mem (.fvar (c+1)) (.fvar 0)
  let EE := E.shifted.weaken (fun q hq => List.mem_cons_of_mem premise hq)
  have out := successorRightAt EE (g+1) (h+1) (a+1) (b+1) (c+1) 0
    (up (orderRightShift g b hg) premise)
    (up (Ordinal.successorShift b c hs) premise)
    (up (exactShift g h a b hx) premise) (assumption (by simp [premise]))
  convert impIntro out using 1 <;> (dsimp [premise,hasOutput] <;> isoSyntax)

#print axioms successorGraphLeftTotal
#print axioms successorGraphRightTotal
end M6.PA.RelationalSource.PairGraph
