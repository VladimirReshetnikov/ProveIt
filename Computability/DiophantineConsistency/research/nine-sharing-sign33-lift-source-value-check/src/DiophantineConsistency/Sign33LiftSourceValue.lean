import DiophantineConsistency.Sign33LiftTerminals
import DiophantineConsistency.Sign33LiftFiveNorms
import DiophantineConsistency.Norm38StaticCarrierConditional

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33LiftSourceValue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel SharingNormTrace SharingTopology38
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem allcuts_imply_value (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    Carrier65.value (fun j => ι (ports j))
      (fun j => ι (v (Fin.castLE (by decide : 15 ≤ 34) (Fin.succ j)) + 1)) = 0 := by
  have h := Norm38Reference.static_terminals_norms_imply_value ports (Sign33Lift38.lift v)
    (Sign33LiftTerminals.terminals ports v hc) (Sign33LiftFiveNorms.five_norms ports v hc)
  simpa only [Sign33Lift38.lift_inputs] using h
end DiophantineConsistency.Sign33LiftSourceValue
#print axioms DiophantineConsistency.Sign33LiftSourceValue.allcuts_imply_value
