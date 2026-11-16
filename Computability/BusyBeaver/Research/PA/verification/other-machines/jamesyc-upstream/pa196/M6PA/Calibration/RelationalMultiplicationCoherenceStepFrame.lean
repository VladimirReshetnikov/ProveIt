module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationCoherenceSuccessor
@[expose] public section

namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

structure MultiplicationCoherenceStepFrame (Γ : List Form) (p x : Nat) where
  addition : ND.Proof Γ addCoherenceStatement
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  strict : ND.Proof Γ closedStrictSeparation
  inclusive : ND.Proof Γ closedInclusiveSeparation
  domain : ND.Proof Γ (Ordinal.domain (.fvar p))
  successor : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar x))
  hypothesis : ND.Proof Γ (mulCoherence (.fvar p))

def MultiplicationCoherenceStepFrame.weaken {Γ Δ : List Form} {p x : Nat}
    (I : MultiplicationCoherenceStepFrame Γ p x) (inc : ∀ t,t∈Γ→t∈Δ) :
    MultiplicationCoherenceStepFrame Δ p x where
  addition := ND.weaken I.addition inc
  equality := I.equality.weaken inc
  empty := ND.weaken I.empty inc
  adjunction := ND.weaken I.adjunction inc
  strict := ND.weaken I.strict inc
  inclusive := ND.weaken I.inclusive inc
  domain := ND.weaken I.domain inc
  successor := ND.weaken I.successor inc
  hypothesis := ND.weaken I.hypothesis inc

def MultiplicationCoherenceStepFrame.shift {Γ : List Form} {p x : Nat}
    (I : MultiplicationCoherenceStepFrame Γ p x) :
    MultiplicationCoherenceStepFrame (shifted Γ) (p+1) (x+1) where
  addition := additionCoherenceClosedShift I.addition
  equality := I.equality.shifted
  empty := emptyClosedShift I.empty
  adjunction := adjunctionClosedShift I.adjunction
  strict := predecessorClosedSeparationShift I.strict
  inclusive := additionInclusiveSeparationShift I.inclusive
  domain := Ordinal.domainShift p I.domain
  successor := Ordinal.successorShift p x I.successor
  hypothesis := mulCoherenceShift p I.hypothesis

def mulCoherenceSuccessorPoint {Γ : List Form} (p x y b c r s : Nat)
    (I : MultiplicationCoherenceStepFrame Γ p x) :
    ND.Proof Γ (mulCoherencePoint (.fvar x) (.fvar y) (.fvar b) (.fvar c) (.fvar r) (.fvar s)) := by
  apply impIntro
  let premise : Form := mulCoherencePremise (.fvar x) (.fvar y) (.fvar b) (.fvar c) (.fvar r) (.fvar s)
  have h : ND.Proof (premise::Γ) premise := assumption (by simp)
  let J := I.weaken (fun t ht => List.mem_cons_of_mem premise ht)
  have h1 := andRight h
  have h2 := andRight h1
  have h3 := andRight h2
  have h4 := andRight h3
  have h5 := andRight h4
  exact multiplicationSuccessorCoherence J.equality p x y b c r s J.addition J.empty J.adjunction J.strict J.inclusive
    J.domain (andLeft h) (andLeft h1) (andLeft h2) J.successor J.hypothesis
    (andLeft h3) (andLeft h4) (andLeft h5) (andRight h5)

#print axioms MultiplicationCoherenceStepFrame.shift
#print axioms mulCoherenceSuccessorPoint
end M6.PA.RelationalSource.PairGraph
