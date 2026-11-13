import FreshCarrierSpheres

/-! Forward norm extraction at abstract difference-ring inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38GenericUnitNorms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem carrier_zero_unitNorms (p : Fin 4 → DiffRing V) (v : Fin 14 → DiffRing V)
    (hb : (0 : DiffRing V) < p 0) (hv : ∀ j, (0 : DiffRing V) < v j)
    (hz : Carrier65.value p v = 0) :
    let d := Carrier65.core p v
    d.P=1 ∧ d.Q=1 ∧ d.U=1 ∧ Carrier65.strong d=1 ∧ d.W=1 := by
  exact (FreshCarrierSpheres.value65_zero_iff_norms
    FreshCarrierSpheres.modelFacts p v hb hv).mp hz
end DiophantineConsistency.Norm38GenericUnitNorms
#print axioms DiophantineConsistency.Norm38GenericUnitNorms.carrier_zero_unitNorms
