import DiophantineConsistency.SharingForward33

/-! Generic semiring constructor projection, full coordinate 28. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33ForwardCoordinate28

theorem project {S : Type*} [CommSemiring S] (ports : Fin 4 → S) (u : Fin 14 → S)
    (gap tau inner value negative : S) :
    (Fin.cons (1 : S) (SharingForward33.witnessCoordinates ports u gap tau inner value negative) : Fin 34 → S) 28 =
      SharingForward38.witnessCoordinates ports u 29 := by
  have hindex : (27 : Fin 33).succ = (28 : Fin 34) := by decide
  rw [←hindex, Fin.cons_succ]
  rfl
end DiophantineConsistency.Sign33ForwardCoordinate28
#print axioms DiophantineConsistency.Sign33ForwardCoordinate28.project
