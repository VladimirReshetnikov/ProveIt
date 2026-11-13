import DiophantineConsistency.Sign33AbstractTuple

/-! Generic tuple and concrete constructor full-coordinate 32. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33AbstractProjection32

theorem template {S : Type*} [One S] (u : Fin 14 → S) (w : Fin 38 → S)
    (gap tau inner value negative : S) :
    (Fin.cons (1 : S) (Sign33AbstractTuple.tuple u w gap tau inner value negative) : Fin 34 → S) 32 = w 35 := by
  have hindex : (31 : Fin 33).succ = (32 : Fin 34) := by decide
  rw [←hindex, Fin.cons_succ]
  rfl

theorem project {S : Type*} [CommSemiring S] (ports : Fin 4 → S) (u : Fin 14 → S)
    (gap tau inner value negative : S) :
    (Fin.cons (1 : S) (SharingForward33.witnessCoordinates ports u gap tau inner value negative) : Fin 34 → S) 32 =
      SharingForward38.witnessCoordinates ports u 35 := by
  exact template u (SharingForward38.witnessCoordinates ports u) gap tau inner value negative
end DiophantineConsistency.Sign33AbstractProjection32
#print axioms DiophantineConsistency.Sign33AbstractProjection32.template
#print axioms DiophantineConsistency.Sign33AbstractProjection32.project
