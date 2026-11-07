import DiophantineConsistency.SharingForward33

/-! Generic semiring constructor projection, full coordinate 22. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33ForwardCoordinate22

theorem project {S : Type*} [CommSemiring S] (ports : Fin 4 → S) (u : Fin 14 → S)
    (gap tau inner value negative : S) :
    (Fin.cons (1 : S) (SharingForward33.witnessCoordinates ports u gap tau inner value negative) : Fin 34 → S) 22 =
      SharingForward38.witnessCoordinates ports u 21 := by
  have hindex : (21 : Fin 33).succ = (22 : Fin 34) := by decide
  rw [←hindex, Fin.cons_succ]
  rfl
end DiophantineConsistency.Sign33ForwardCoordinate22
#print axioms DiophantineConsistency.Sign33ForwardCoordinate22.project
