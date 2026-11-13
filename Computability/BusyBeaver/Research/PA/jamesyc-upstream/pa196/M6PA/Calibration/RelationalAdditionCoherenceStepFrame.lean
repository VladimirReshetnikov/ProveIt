module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionCoherenceSuccessor
@[expose] public section

namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

structure AdditionCoherenceStepFrame (Γ : List Form) (p x : Nat) where
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  strict : ND.Proof Γ closedStrictSeparation
  inclusive : ND.Proof Γ closedInclusiveSeparation
  domain : ND.Proof Γ (Ordinal.domain (.fvar p))
  successor : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar x))
  hypothesis : ND.Proof Γ (addCoherence (.fvar p))

def AdditionCoherenceStepFrame.weaken {Γ Δ : List Form} {p x : Nat}
    (I : AdditionCoherenceStepFrame Γ p x) (inc : ∀ t,t∈Γ→t∈Δ) :
    AdditionCoherenceStepFrame Δ p x where
  equality := I.equality.weaken inc
  empty := ND.weaken I.empty inc
  adjunction := ND.weaken I.adjunction inc
  strict := ND.weaken I.strict inc
  inclusive := ND.weaken I.inclusive inc
  domain := ND.weaken I.domain inc
  successor := ND.weaken I.successor inc
  hypothesis := ND.weaken I.hypothesis inc

def AdditionCoherenceStepFrame.shift {Γ : List Form} {p x : Nat}
    (I : AdditionCoherenceStepFrame Γ p x) :
    AdditionCoherenceStepFrame (shifted Γ) (p+1) (x+1) where
  equality := I.equality.shifted
  empty := emptyClosedShift I.empty
  adjunction := adjunctionClosedShift I.adjunction
  strict := predecessorClosedSeparationShift I.strict
  inclusive := additionInclusiveSeparationShift I.inclusive
  domain := Ordinal.domainShift p I.domain
  successor := Ordinal.successorShift p x I.successor
  hypothesis := addCoherenceShift p I.hypothesis

def addCoherenceSuccessorPoint {Γ : List Form} (p x y b c r s : Nat)
    (I : AdditionCoherenceStepFrame Γ p x) :
    ND.Proof Γ (addCoherencePoint (.fvar x) (.fvar y) (.fvar b) (.fvar c) (.fvar r) (.fvar s)) := by
  apply impIntro
  let premise : Form := addCoherencePremise (.fvar x) (.fvar y) (.fvar b) (.fvar c) (.fvar r) (.fvar s)
  have h : ND.Proof (premise::Γ) premise := assumption (by simp)
  let J := I.weaken (fun t ht => List.mem_cons_of_mem premise ht)
  have h1 := andRight h
  have h2 := andRight h1
  have h3 := andRight h2
  have h4 := andRight h3
  have h5 := andRight h4
  exact additionSuccessorCoherence J.equality p x y b c r s J.empty J.adjunction J.strict J.inclusive
    J.domain (andLeft h) (andLeft h1) (andLeft h2) J.successor J.hypothesis
    (andLeft h3) (andLeft h4) (andLeft h5) (andRight h5)

#print axioms AdditionCoherenceStepFrame.shift
#print axioms addCoherenceSuccessorPoint
end M6.PA.RelationalSource.PairGraph
