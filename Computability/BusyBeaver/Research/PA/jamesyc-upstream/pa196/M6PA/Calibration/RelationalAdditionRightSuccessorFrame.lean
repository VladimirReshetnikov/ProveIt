module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRightSuccessor
@[expose] public section

/-! Explicit movable proof data for right-successor induction. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.successor

structure AdditionRightSuccessorStepFrame (Γ : List Form) (p x : Nat) where
  basis : AdditionRightSuccessorBasis Γ
  domain : ND.Proof Γ (Ordinal.domain (.fvar p))
  successor : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar x))
  hypothesis : ND.Proof Γ (addRightSuccessor (.fvar p))

def AdditionRightSuccessorStepFrame.shift {Γ : List Form} {p x : Nat}
    (I : AdditionRightSuccessorStepFrame Γ p x) : AdditionRightSuccessorStepFrame (shifted Γ) (p+1) (x+1) :=
  ⟨I.basis.shift,Ordinal.domainShift p I.domain,
    Ordinal.successorShift p x I.successor,addRightSuccessorShift p I.hypothesis⟩

def AdditionRightSuccessorStepFrame.weaken {Γ Δ : List Form} {p x : Nat}
    (I : AdditionRightSuccessorStepFrame Γ p x) (inc : ∀ q,q∈Γ→q∈Δ) :
    AdditionRightSuccessorStepFrame Δ p x :=
  ⟨I.basis.weaken inc,ND.weaken I.domain inc,ND.weaken I.successor inc,ND.weaken I.hypothesis inc⟩

structure AdditionRightSuccessorOutputFrame (Γ : List Form) (p x b c r s v : Nat) where
  step : AdditionRightSuccessorStepFrame Γ p x
  leftDomain : ND.Proof Γ (Ordinal.domain (.fvar b))
  rightDomain : ND.Proof Γ (Ordinal.domain (.fvar c))
  outputDomain : ND.Proof Γ (Ordinal.domain (.fvar r))
  baseSuccessor : ND.Proof Γ (Ordinal.successor (.fvar b) (.fvar c))
  leftResult : ND.Proof Γ (addResult (.fvar x) (.fvar b) (.fvar r))
  rightResult : ND.Proof Γ (addResult (.fvar x) (.fvar c) (.fvar s))
  outputSuccessor : ND.Proof Γ (Ordinal.successor (.fvar r) (.fvar v))

def AdditionRightSuccessorOutputFrame.shift {Γ : List Form} {p x b c r s v : Nat}
    (I : AdditionRightSuccessorOutputFrame Γ p x b c r s v) :
    AdditionRightSuccessorOutputFrame (shifted Γ) (p+1) (x+1) (b+1) (c+1) (r+1) (s+1) (v+1) :=
  ⟨I.step.shift,Ordinal.domainShift b I.leftDomain,Ordinal.domainShift c I.rightDomain,
    Ordinal.domainShift r I.outputDomain,Ordinal.successorShift b c I.baseSuccessor,
    coherenceResultShift x b r I.leftResult,coherenceResultShift x c s I.rightResult,
    Ordinal.successorShift r v I.outputSuccessor⟩

def AdditionRightSuccessorOutputFrame.weaken {Γ Δ : List Form} {p x b c r s v : Nat}
    (I : AdditionRightSuccessorOutputFrame Γ p x b c r s v) (inc : ∀ q,q∈Γ→q∈Δ) :
    AdditionRightSuccessorOutputFrame Δ p x b c r s v :=
  ⟨I.step.weaken inc,ND.weaken I.leftDomain inc,ND.weaken I.rightDomain inc,
    ND.weaken I.outputDomain inc,ND.weaken I.baseSuccessor inc,
    ND.weaken I.leftResult inc,ND.weaken I.rightResult inc,ND.weaken I.outputSuccessor inc⟩

#print axioms AdditionRightSuccessorOutputFrame.shift
end M6.PA.RelationalSource.PairGraph
