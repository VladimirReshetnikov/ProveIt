import DiophantineConsistency.Sign33AbstractTuple

/-! Instantiate the abstract tuple without expanding its 38-coordinate argument. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33AbstractProjection22

theorem project {S : Type*} [CommSemiring S] (ports : Fin 4 → S) (u : Fin 14 → S)
    (gap tau inner value negative : S) :
    (Fin.cons (1 : S) (SharingForward33.witnessCoordinates ports u gap tau inner value negative) : Fin 34 → S) 22 =
      SharingForward38.witnessCoordinates ports u 21 := by
  exact Sign33AbstractTuple.project22 u (SharingForward38.witnessCoordinates ports u) gap tau inner value negative
end DiophantineConsistency.Sign33AbstractProjection22
#print axioms DiophantineConsistency.Sign33AbstractProjection22.project
