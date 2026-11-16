module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoPredecessorTotalRules
@[expose] public section

/-! Universal left/right totality of a strict predecessor graph cut. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def predecessorGraphLeftTotal {Γ : List Form} (g h a p : Nat)
    (hl : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a)))
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar p) (.fvar g) (.fvar h))) :
    ND.Proof Γ (graphLeftTotal (.fvar h) (.fvar p)) := by
  apply allIntro
  let premise : Form := mem (.fvar (p+1)) (.fvar 0)
  have out := predecessorLeftAt (g+1) (h+1) (a+1) (p+1) 0
    (up (orderLeftShift g a hl) premise) (up (Ordinal.successorShift p a hs) premise)
    (up (strictRestrictionShift p g h hr) premise) (assumption (by simp [premise]))
  convert impIntro out using 1 <;> (dsimp [premise,hasOutput] <;> isoSyntax)

def predecessorGraphRightTotal {Γ : List Form} (g h b p q : Nat)
    (ht : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)))
    (ho : ND.Proof Γ (graphOrder (.fvar g)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar q) (.fvar b)))
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar p) (.fvar g) (.fvar h)))
    (hpq : ND.Proof Γ (edge (.fvar g) (.fvar p) (.fvar q))) :
    ND.Proof Γ (graphRightTotal (.fvar h) (.fvar q)) := by
  apply allIntro
  let premise : Form := mem (.fvar (q+1)) (.fvar 0)
  have ee : ND.Proof (premise::shifted Γ) (edge (.fvar (g+1)) (.fvar (p+1)) (.fvar (q+1))) := by
    have hh := up (shiftProof hpq) premise
    convert hh using 1 <;> isoSyntax
  have out := predecessorRightAt (g+1) (h+1) (b+1) (p+1) (q+1) 0
    (up (orderRightShift g b ht) premise) (up (orderOrderShift g ho) premise)
    (up (Ordinal.successorShift q b hs) premise) (up (strictRestrictionShift p g h hr) premise)
    ee (assumption (by simp [premise]))
  convert impIntro out using 1 <;> (dsimp [premise] <;> isoSyntax)

#print axioms predecessorGraphLeftTotal
#print axioms predecessorGraphRightTotal
end M6.PA.RelationalSource.PairGraph
