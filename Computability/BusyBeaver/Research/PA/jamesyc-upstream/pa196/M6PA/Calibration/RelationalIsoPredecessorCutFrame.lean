module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoPredecessorBijection
public import M6PA.Calibration.RelationalIsoSuccessorFrame
public import M6PA.Calibration.RelationalGraphRestrictionSupplier
@[expose] public section

/-! Explicit finite inputs to construct a predecessor isomorphism by Separation. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def predecessorClosedSeparationShift {Γ : List Form}
    (h : ND.Proof Γ closedStrictSeparation) :
    ND.Proof (shifted Γ) closedStrictSeparation := by
  convert shiftProof h using 1 <;>
    (dsimp [closedStrictSeparation,closeParameter] <;> restrictionSyntax)

structure PredecessorCutFrame (Γ : List Form) (g a b p q : Nat) where
  equality : FormulaEquality Γ
  separation : ND.Proof Γ closedStrictSeparation
  graph : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b))
  leftSuccessor : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a))
  rightSuccessor : ND.Proof Γ (Ordinal.successor (.fvar q) (.fvar b))
  endpoint : ND.Proof Γ (edge (.fvar g) (.fvar p) (.fvar q))

def PredecessorCutFrame.weaken {Γ Δ : List Form} {g a b p q : Nat}
    (I : PredecessorCutFrame Γ g a b p q) (inc : ∀ t,t ∈ Γ → t ∈ Δ) :
    PredecessorCutFrame Δ g a b p q where
  equality := I.equality.weaken inc
  separation := ND.weaken I.separation inc
  graph := ND.weaken I.graph inc
  leftSuccessor := ND.weaken I.leftSuccessor inc
  rightSuccessor := ND.weaken I.rightSuccessor inc
  endpoint := ND.weaken I.endpoint inc

def PredecessorCutFrame.shift {Γ : List Form} {g a b p q : Nat}
    (I : PredecessorCutFrame Γ g a b p q) :
    PredecessorCutFrame (shifted Γ) (g+1) (a+1) (b+1) (p+1) (q+1) where
  equality := I.equality.shifted
  separation := predecessorClosedSeparationShift I.separation
  graph := orderBijectionShift g a b I.graph
  leftSuccessor := Ordinal.successorShift p a I.leftSuccessor
  rightSuccessor := Ordinal.successorShift q b I.rightSuccessor
  endpoint := by convert shiftProof I.endpoint using 1 <;> isoSyntax

#print axioms predecessorClosedSeparationShift
#print axioms PredecessorCutFrame.shift
end M6.PA.RelationalSource.PairGraph
