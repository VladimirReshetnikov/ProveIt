module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionCoverageExtension
@[expose] public section

/-! Finite proof data for constructing one actual composition-prefix extension. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def compositionPrefixShift {Γ : List Form} (g h n k : Nat)
    (hc : ND.Proof Γ (compositionPrefix (.fvar g) (.fvar h) (.fvar n) (.fvar k))) :
    ND.Proof (shifted Γ) (compositionPrefix (.fvar (g+1)) (.fvar (h+1)) (.fvar (n+1)) (.fvar (k+1))) := by
  convert shiftProof hc using 1 <;> compositionSyntax

structure CompositionFrame (Γ : List Form) (g h n s k y z : Nat) where
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  graph : ND.Proof Γ (compositionPrefix (.fvar g) (.fvar h) (.fvar n) (.fvar k))
  successor : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s))
  leftEdge : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar y))
  rightEdge : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar z))

def CompositionFrame.weaken {Γ Δ : List Form} {g h n s k y z : Nat}
    (I : CompositionFrame Γ g h n s k y z) (inc : ∀ p, p ∈ Γ → p ∈ Δ) :
    CompositionFrame Δ g h n s k y z where
  equality := I.equality.weaken inc
  empty := ND.weaken I.empty inc
  adjunction := ND.weaken I.adjunction inc
  graph := ND.weaken I.graph inc
  successor := ND.weaken I.successor inc
  leftEdge := ND.weaken I.leftEdge inc
  rightEdge := ND.weaken I.rightEdge inc

def CompositionFrame.shift {Γ : List Form} {g h n s k y z : Nat}
    (I : CompositionFrame Γ g h n s k y z) :
    CompositionFrame (shifted Γ) (g+1) (h+1) (n+1) (s+1) (k+1) (y+1) (z+1) where
  equality := I.equality.shifted
  empty := emptyClosedShift I.empty
  adjunction := adjunctionClosedShift I.adjunction
  graph := compositionPrefixShift g h n k I.graph
  successor := Ordinal.successorShift n s I.successor
  leftEdge := by convert shiftProof I.leftEdge using 1 <;> compositionSyntax
  rightEdge := by convert shiftProof I.rightEdge using 1 <;> compositionSyntax

#print axioms compositionPrefixShift
#print axioms CompositionFrame.weaken
#print axioms CompositionFrame.shift
end M6.PA.RelationalSource.PairGraph
