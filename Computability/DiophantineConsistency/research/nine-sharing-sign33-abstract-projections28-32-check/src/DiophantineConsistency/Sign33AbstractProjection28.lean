import DiophantineConsistency.Sign33AbstractTuple

/-! Generic tuple and concrete constructor full-coordinate 28. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33AbstractProjection28

theorem template {S : Type*} [One S] (u : Fin 14 → S) (w : Fin 38 → S)
    (gap tau inner value negative : S) :
    (Fin.cons (1 : S) (Sign33AbstractTuple.tuple u w gap tau inner value negative) : Fin 34 → S) 28 = w 29 := by
  have hindex : (27 : Fin 33).succ = (28 : Fin 34) := by decide
  rw [←hindex, Fin.cons_succ]
  rfl

theorem project {S : Type*} [CommSemiring S] (ports : Fin 4 → S) (u : Fin 14 → S)
    (gap tau inner value negative : S) :
    (Fin.cons (1 : S) (SharingForward33.witnessCoordinates ports u gap tau inner value negative) : Fin 34 → S) 28 =
      SharingForward38.witnessCoordinates ports u 29 := by
  exact template u (SharingForward38.witnessCoordinates ports u) gap tau inner value negative
end DiophantineConsistency.Sign33AbstractProjection28
#print axioms DiophantineConsistency.Sign33AbstractProjection28.template
#print axioms DiophantineConsistency.Sign33AbstractProjection28.project
