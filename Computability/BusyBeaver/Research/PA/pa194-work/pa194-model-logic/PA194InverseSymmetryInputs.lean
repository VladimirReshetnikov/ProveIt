import PA194InverseClosedShift
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194InverseSymmetryInputs
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194InverseClosedTemplate

structure Inputs (Γ : List Form) where
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  intersection : ND.Proof Γ Ordinal.intersectionFormula
  separation : ND.Proof Γ closedInverseSeparation

def Inputs.weaken {Γ Δ : List Form} (I : Inputs Γ) (h : ∀ p, p ∈ Γ → p ∈ Δ) : Inputs Δ :=
  ⟨I.equality.weaken h, ND.weaken I.empty h, ND.weaken I.adjunction h,
    ND.weaken I.intersection h, ND.weaken I.separation h⟩

def Inputs.shift {Γ : List Form} (I : Inputs Γ) : Inputs (ND.shifted Γ) :=
  ⟨I.equality.shifted, emptyClosedShift I.empty, adjunctionClosedShift I.adjunction,
    Ordinal.intersectionAxiomShift I.intersection,
    closedInverseSeparation_shift ▸ ND.shiftProof I.separation⟩

def Inputs.inverse {Γ : List Form} (I : Inputs Γ) (a b : Nat)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof Γ (orderIso (.fvar b) (.fvar a)) :=
  inverseIsoSymmetry I.equality a b I.empty I.adjunction I.intersection
    (inverseClosedAt a I.separation) hi ha
#print axioms Inputs.shift
#print axioms Inputs.inverse
end PA194InverseSymmetryInputs
