import DiophantineConsistency.ForwardWitness38
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38Forward
/-- The natural constructor preserves the first fourteen input coordinates. -/
theorem forward_prefix {S : Type*} [CommSemiring S]
    (ports : Fin 4 → S) (u : Fin 14 → S) (j : Fin 14) :
    SharingForward38.witnessCoordinates ports u
      (Fin.castLE (by decide : 14 ≤ 38) j) = u j := by
  fin_cases j <;> simp [SharingForward38.witnessCoordinates]


end DiophantineConsistency.Norm38Forward
