import DiophantineConsistency.SharingForward33

/-! An abstract tuple template keeps the supplied 38 coordinates opaque. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33AbstractTuple

def tuple {S : Type*} (u : Fin 14 → S) (w : Fin 38 → S)
    (gap tau inner value negative : S) : Fin 33 → S :=
  ![u 0, u 1, u 2, u 3, u 4, u 5, u 6, u 7, u 8, u 9, u 10, u 11, u 12, u 13, w 14, w 15, w 16, w 17, w 18, w 19, w 20, w 21, w 22, w 23, w 24, gap, tau, w 29, inner, value, w 34, w 35, negative]

theorem project22 {S : Type*} [One S] (u : Fin 14 → S) (w : Fin 38 → S)
    (gap tau inner value negative : S) :
    (Fin.cons (1 : S) (tuple u w gap tau inner value negative) : Fin 34 → S) 22 = w 21 := by
  have hindex : (21 : Fin 33).succ = (22 : Fin 34) := by decide
  rw [←hindex, Fin.cons_succ]
  rfl
end DiophantineConsistency.Sign33AbstractTuple
#print axioms DiophantineConsistency.Sign33AbstractTuple.project22
