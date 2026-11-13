import DiophantineConsistency.Norm38ReferenceBase

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel SharingNormTrace SharingTopology38
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem initial_node15 (ports : Fin 4 → V) (w : Fin 38 → V) :
    pairValue ι (NormAssignment38.assignment ports w 15) =
      reference (fun j => ι (ports j))
        (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1)) 15 := by
  simp [reference, NormAssignment38.assignment, pairValue, map_add, map_one, map_ofNat]

theorem initial_node16 (ports : Fin 4 → V) (w : Fin 38 → V) :
    pairValue ι (NormAssignment38.assignment ports w 16) =
      reference (fun j => ι (ports j))
        (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1)) 16 := by
  simp [reference, NormAssignment38.assignment, pairValue, map_add, map_one, map_ofNat]

theorem initial_node17 (ports : Fin 4 → V) (w : Fin 38 → V) :
    pairValue ι (NormAssignment38.assignment ports w 17) =
      reference (fun j => ι (ports j))
        (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1)) 17 := by
  simp [reference, NormAssignment38.assignment, pairValue, map_add, map_one, map_ofNat]


end DiophantineConsistency.Norm38Reference
