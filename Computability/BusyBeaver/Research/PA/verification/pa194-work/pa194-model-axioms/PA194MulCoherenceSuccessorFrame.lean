import PA194MulCoherenceSuccessor
import PA194CancelClosedShift
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194MulCoherence
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

structure StepFrame (Γ : List Form) (p x : Nat) where
  addition : ND.Proof Γ addCoherenceStatement
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  strict : ND.Proof Γ closedStrictSeparation
  inclusive : ND.Proof Γ closedInclusiveSeparation
  domain : ND.Proof Γ (Ordinal.domain (.fvar p))
  successor : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar x))
  hypothesis : ND.Proof Γ (coherence (.fvar p))

def StepFrame.weaken {Γ Δ : List Form} {p x : Nat} (I : StepFrame Γ p x)
    (inc : ∀ t, t ∈ Γ → t ∈ Δ) : StepFrame Δ p x where
  addition := ND.weaken I.addition inc
  equality := I.equality.weaken inc
  empty := ND.weaken I.empty inc
  adjunction := ND.weaken I.adjunction inc
  strict := ND.weaken I.strict inc
  inclusive := ND.weaken I.inclusive inc
  domain := ND.weaken I.domain inc
  successor := ND.weaken I.successor inc
  hypothesis := ND.weaken I.hypothesis inc

def StepFrame.shift {Γ : List Form} {p x : Nat} (I : StepFrame Γ p x) :
    StepFrame (ND.shifted Γ) (p+1) (x+1) where
  addition := additionClosedShift I.addition
  equality := I.equality.shifted
  empty := emptyClosedShift I.empty
  adjunction := adjunctionClosedShift I.adjunction
  strict := by simpa only [PA194CancelClosedShift.closedStrictSeparation_shift] using ND.shiftProof I.strict
  inclusive := by simpa only [PA194InclusiveSeparationClosure.closedSep_shift] using ND.shiftProof I.inclusive
  domain := Ordinal.domainShift p I.domain
  successor := Ordinal.successorShift p x I.successor
  hypothesis := PA194MulCoherence.shift p I.hypothesis

def successorPoint {Γ : List Form} (p x y b c r s : Nat) (I : StepFrame Γ p x) :
    ND.Proof Γ (point (.fvar x) (.fvar y) (.fvar b) (.fvar c) (.fvar r) (.fvar s)) := by
  unfold point
  apply ND.impIntro
  let q : Form := premise (.fvar x) (.fvar y) (.fvar b) (.fvar c) (.fvar r) (.fvar s)
  have h : ND.Proof (q::Γ) q := ND.assumption (by simp)
  let J := I.weaken (fun t ht => List.mem_cons_of_mem q ht)
  have h1 := ND.andRight h
  have h2 := ND.andRight h1
  have h3 := ND.andRight h2
  have h4 := ND.andRight h3
  have h5 := ND.andRight h4
  exact successorCoherence J.equality p x y b c r s J.addition J.empty J.adjunction J.strict J.inclusive
    J.domain (ND.andLeft h) (ND.andLeft h1) (ND.andLeft h2) J.successor J.hypothesis
    (ND.andLeft h3) (ND.andLeft h4) (ND.andLeft h5) (ND.andRight h5)
#print axioms StepFrame.shift
#print axioms successorPoint
end PA194MulCoherence
