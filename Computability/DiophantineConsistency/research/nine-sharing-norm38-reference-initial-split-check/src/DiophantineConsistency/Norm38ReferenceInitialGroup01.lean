import DiophantineConsistency.Norm38ReferenceBase

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel SharingNormTrace SharingTopology38
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem initial_node03 (ports : Fin 4 → V) (w : Fin 38 → V) :
    pairValue ι (NormAssignment38.assignment ports w 3) =
      reference (fun j => ι (ports j))
        (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1)) 3 := by
  simp [reference, NormAssignment38.assignment, pairValue, map_add, map_one, map_ofNat]

theorem initial_node04 (ports : Fin 4 → V) (w : Fin 38 → V) :
    pairValue ι (NormAssignment38.assignment ports w 4) =
      reference (fun j => ι (ports j))
        (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1)) 4 := by
  simp [reference, NormAssignment38.assignment, pairValue, map_add, map_one, map_ofNat]

theorem initial_node05 (ports : Fin 4 → V) (w : Fin 38 → V) :
    pairValue ι (NormAssignment38.assignment ports w 5) =
      reference (fun j => ι (ports j))
        (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1)) 5 := by
  simp [reference, NormAssignment38.assignment, pairValue, map_add, map_one, map_ofNat]


end DiophantineConsistency.Norm38Reference
