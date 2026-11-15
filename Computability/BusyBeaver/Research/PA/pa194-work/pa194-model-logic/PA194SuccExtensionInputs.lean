import PA194FoundationOrderIsoSuccessor
import PA194FoundationOrdinalSuccessorDerivation
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194SuccExtensionInputs
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

structure Inputs (Γ : List Form) where
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  intersection : ND.Proof Γ Ordinal.intersectionFormula

def Inputs.weaken {Γ Δ : List Form} (I : Inputs Γ) (h : ∀ p, p ∈ Γ → p ∈ Δ) : Inputs Δ :=
  ⟨I.equality.weaken h,ND.weaken I.empty h,ND.weaken I.adjunction h,ND.weaken I.intersection h⟩

def Inputs.shift {Γ : List Form} (I : Inputs Γ) : Inputs (ND.shifted Γ) :=
  ⟨I.equality.shifted,emptyClosedShift I.empty,adjunctionClosedShift I.adjunction,
    Ordinal.intersectionAxiomShift I.intersection⟩

def Inputs.successorExists {Γ : List Form} (I : Inputs Γ) (a : Nat)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a))) : ND.Proof Γ (Ordinal.domainSuccessorExists (.fvar a)) :=
  Ordinal.domainSuccessorFromAxioms I.equality.core I.equality.transitive I.intersection I.adjunction (.fvar a) ha

def Inputs.extend {Γ : List Form} (I : Inputs Γ) (a b c d : Nat)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a))) (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar c)))
    (ht : ND.Proof Γ (Ordinal.successor (.fvar b) (.fvar d)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) : ND.Proof Γ (orderIso (.fvar c) (.fvar d)) :=
  orderIsoSuccessor I.equality a b c d I.empty I.adjunction ha hb hs ht hi
#print axioms Inputs.successorExists
#print axioms Inputs.extend
end PA194SuccExtensionInputs
