import FreshCarrierSpheres

/-! Candidate model-norm extraction, isolated from syntax and witnesses. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38CarrierUnitNorms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem carrier_zero_unitNorms (ports : Fin 4 → V) (u : Fin 14 → V)
    (hb : (0 : DiffRing V) < ι (ports 0))
    (hz : Carrier65.value (fun j => ι (ports j)) (fun j => ι (u j+1)) = 0) :
    let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
    d.P=1 ∧ d.Q=1 ∧ d.U=1 ∧ Carrier65.strong d=1 ∧ d.W=1 := by
  have hpositive : ∀ j, (0 : DiffRing V) < ι (u j+1) := fun j =>
    ι_pos (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
  exact (FreshCarrierSpheres.value65_zero_iff_norms FreshCarrierSpheres.modelFacts
    (fun j => ι (ports j)) (fun j => ι (u j+1)) hb hpositive).mp hz
end DiophantineConsistency.Norm38CarrierUnitNorms
#print axioms DiophantineConsistency.Norm38CarrierUnitNorms.carrier_zero_unitNorms
