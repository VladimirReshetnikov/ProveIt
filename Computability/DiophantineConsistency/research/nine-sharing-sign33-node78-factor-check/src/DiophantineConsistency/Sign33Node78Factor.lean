import DiophantineConsistency.NormAssignment38

/-! Generic node78 identity with node76 kept as an abstract signed value. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33Node78Factor
open SharingGateModel

theorem node78 {S R : Type*} [CommSemiring S] [CommRing R]
    (embed : S →+* R) (ports : Fin 4 → S) (w : Fin 38 → S) :
    pairValue embed (NormAssignment38.assignment ports w 78) =
      embed (w 35) * pairValue embed (NormAssignment38.assignment ports w 76) +
        embed (w 12+1)*embed (w 12+1) := by
  simp [NormAssignment38.assignment, pairValue, pairCompute, map_add, map_mul] <;> ring
end DiophantineConsistency.Sign33Node78Factor
#print axioms DiophantineConsistency.Sign33Node78Factor.node78
