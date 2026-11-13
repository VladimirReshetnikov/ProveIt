module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionExistsStep
public import M6PA.Calibration.RelationalIsoCompositionEdgeTotal
public import M6PA.Calibration.RelationalIsoInverseGuardedStep
@[expose] public section

/-! The composition successor step retains the explicit subset(n,a) guard. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def compositionGuardedStep {Γ : List Form} (E : FormulaEquality Γ) (g h a b n s : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hg : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a)))
    (hh : ND.Proof Γ (graphLeftTotal (.fvar h) (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hi : ND.Proof Γ (Ordinal.subset (.fvar n) (.fvar a) 🡒 compositionPrefixExists (.fvar g) (.fvar h) (.fvar n))) :
    ND.Proof Γ (Ordinal.subset (.fvar s) (.fvar a) 🡒 compositionPrefixExists (.fvar g) (.fvar h) (.fvar s)) := by
  apply impIntro
  let d : Form := Ordinal.subset (.fvar s) (.fvar a)
  have hd : ND.Proof (d :: Γ) d := assumption (by simp)
  have ee := E.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have hns := mp (ND.orRight (Ordinal.eqRefl ee.core n)) (andRight (Ordinal.successorAt n s n (up hs d)))
  have hna := Ordinal.subsetAt s a n hd hns
  have hz := compositionOutputAt g h a b n (up ht d) (up hg d) (up hh d) hna
  have hp := mp (inversePredecessorSubset n s a (up hs d) hd) (up hi d)
  exact compositionExistsStep ee g h n s (up hempty d) (up hadj d) (up hs d) hz hp

#print axioms compositionGuardedStep
end M6.PA.RelationalSource.PairGraph
