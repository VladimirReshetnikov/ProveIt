import DiophantineConsistency.Norm38CurrentPortBase
set_option autoImplicit false
namespace DiophantineConsistency.Norm38FinFour
/-- A small abstract finite-function assembly, independent of the port terms. -/
theorem eq_all {α : Sort*} (f g : Fin 4 → α)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h2 : f 2 = g 2) (h3 : f 3 = g 3) :
    ∀ j, f j = g j := by
  intro j
  fin_cases j <;> assumption
end DiophantineConsistency.Norm38FinFour
#print axioms DiophantineConsistency.Norm38FinFour.eq_all
