module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoSuccessorBijection
@[expose] public section

/-! Explicit finite proof inputs for constructing a successor isomorphism. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def orderBijectionShift {Γ : List Form} (g a b : Nat)
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b))) :
    ND.Proof (shifted Γ) (orderBijection (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1))) := by
  convert shiftProof hg using 1 <;> isoSyntax

structure IsoSuccessorFrame (Γ : List Form) (g a b c d : Nat) where
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  graph : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b))
  leftDomain : ND.Proof Γ (Ordinal.domain (.fvar a))
  rightDomain : ND.Proof Γ (Ordinal.domain (.fvar b))
  leftSuccessor : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar c))
  rightSuccessor : ND.Proof Γ (Ordinal.successor (.fvar b) (.fvar d))

def IsoSuccessorFrame.weaken {Γ Δ : List Form} {g a b c d : Nat}
    (I : IsoSuccessorFrame Γ g a b c d) (inc : ∀ p,p ∈ Γ → p ∈ Δ) :
    IsoSuccessorFrame Δ g a b c d where
  equality := I.equality.weaken inc
  empty := ND.weaken I.empty inc
  adjunction := ND.weaken I.adjunction inc
  graph := ND.weaken I.graph inc
  leftDomain := ND.weaken I.leftDomain inc
  rightDomain := ND.weaken I.rightDomain inc
  leftSuccessor := ND.weaken I.leftSuccessor inc
  rightSuccessor := ND.weaken I.rightSuccessor inc

def IsoSuccessorFrame.shift {Γ : List Form} {g a b c d : Nat}
    (I : IsoSuccessorFrame Γ g a b c d) :
    IsoSuccessorFrame (shifted Γ) (g+1) (a+1) (b+1) (c+1) (d+1) where
  equality := I.equality.shifted
  empty := emptyClosedShift I.empty
  adjunction := adjunctionClosedShift I.adjunction
  graph := orderBijectionShift g a b I.graph
  leftDomain := Ordinal.domainShift a I.leftDomain
  rightDomain := Ordinal.domainShift b I.rightDomain
  leftSuccessor := Ordinal.successorShift a c I.leftSuccessor
  rightSuccessor := Ordinal.successorShift b d I.rightSuccessor

#print axioms orderBijectionShift
#print axioms IsoSuccessorFrame.shift
end M6.PA.RelationalSource.PairGraph
