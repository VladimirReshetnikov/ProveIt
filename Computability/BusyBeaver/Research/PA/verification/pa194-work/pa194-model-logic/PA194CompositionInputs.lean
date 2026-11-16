import PA194CompositionClosedShiftFast
import PA194CompositionClosedAt
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194CompositionInputs
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194CompositionClosedTemplate

structure Inputs (Γ : List Form) where
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  intersection : ND.Proof Γ Ordinal.intersectionFormula
  separation : ND.Proof Γ closedCompositionSeparation

def Inputs.weaken {Γ Δ : List Form} (I : Inputs Γ) (h : ∀ p, p ∈ Γ → p ∈ Δ) : Inputs Δ :=
  ⟨I.equality.weaken h, ND.weaken I.empty h, ND.weaken I.adjunction h,
    ND.weaken I.intersection h, ND.weaken I.separation h⟩

def Inputs.shift {Γ : List Form} (I : Inputs Γ) : Inputs (ND.shifted Γ) :=
  ⟨I.equality.shifted, emptyClosedShift I.empty, adjunctionClosedShift I.adjunction,
    Ordinal.intersectionAxiomShift I.intersection,
    closedCompositionSeparation_shift_fast ▸ ND.shiftProof I.separation⟩

def Inputs.compose {Γ : List Form} (I : Inputs Γ) (a b c : Nat)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (h1 : ND.Proof Γ (orderIso (.fvar a) (.fvar b)))
    (h2 : ND.Proof Γ (orderIso (.fvar b) (.fvar c))) :
    ND.Proof Γ (orderIso (.fvar a) (.fvar c)) :=
  compositionIsoTransitivity I.equality a b c I.empty I.adjunction I.intersection
    (compositionClosedAt a I.separation) h1 h2 ha
#print axioms Inputs.shift
#print axioms Inputs.compose
end PA194CompositionInputs
