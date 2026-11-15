import PA194CancelClosedShift
import PA194FoundationIsoCancelClosed
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194CancelInputs
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194CancelClosedShift

structure Inputs (Γ : List Form) where
  equality : FormulaEquality Γ
  separation : ND.Proof Γ closedStrictSeparation

def Inputs.weaken {Γ Δ : List Form} (I : Inputs Γ) (h : ∀ p, p ∈ Γ → p ∈ Δ) : Inputs Δ :=
  ⟨I.equality.weaken h, ND.weaken I.separation h⟩

def Inputs.shift {Γ : List Form} (I : Inputs Γ) : Inputs (ND.shifted Γ) :=
  ⟨I.equality.shifted, closedStrictSeparation_shift ▸ ND.shiftProof I.separation⟩

def Inputs.cancel {Γ : List Form} (I : Inputs Γ) (a b p q : Nat)
    (hd : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hp : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a)))
    (hq : ND.Proof Γ (Ordinal.successor (.fvar q) (.fvar b)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof Γ (orderIso (.fvar p) (.fvar q)) :=
  orderIsoSuccessorCancelClosed I.equality a b p q I.separation hd hp hq hi
#print axioms Inputs.shift
#print axioms Inputs.cancel
end PA194CancelInputs
