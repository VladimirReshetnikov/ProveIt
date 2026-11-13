import DiophantineConsistency.Sign33AbstractTuple

/-! Generic tuple and concrete constructor full-coordinate 21. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33AbstractProjection21

theorem template {S : Type*} [One S] (u : Fin 14 → S) (w : Fin 38 → S)
    (gap tau inner value negative : S) :
    (Fin.cons (1 : S) (Sign33AbstractTuple.tuple u w gap tau inner value negative) : Fin 34 → S) 21 = w 20 := by
  have hindex : (20 : Fin 33).succ = (21 : Fin 34) := by decide
  rw [←hindex, Fin.cons_succ]
  rfl

theorem project {S : Type*} [CommSemiring S] (ports : Fin 4 → S) (u : Fin 14 → S)
    (gap tau inner value negative : S) :
    (Fin.cons (1 : S) (SharingForward33.witnessCoordinates ports u gap tau inner value negative) : Fin 34 → S) 21 =
      SharingForward38.witnessCoordinates ports u 20 := by
  exact template u (SharingForward38.witnessCoordinates ports u) gap tau inner value negative
end DiophantineConsistency.Sign33AbstractProjection21
#print axioms DiophantineConsistency.Sign33AbstractProjection21.template
#print axioms DiophantineConsistency.Sign33AbstractProjection21.project
