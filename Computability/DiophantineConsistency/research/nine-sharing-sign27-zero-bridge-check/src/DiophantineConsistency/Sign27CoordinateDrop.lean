import DiophantineConsistency.Sign27RemainingCuts01

/-! SOURCE-ONLY: explicit-predecessor coordinate inverses. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign27ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def drop {S : Type*} (u : S) (v : Fin 29 → S) : Fin 28 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, u, v 23, v 24, v 25, v 26, v 27, v 28]

theorem lift_drop (v : Fin 29 → V) (u : V)
    (hx : v 21 = u + 1) (hy : v 22 = u * (u + 2)) :
    Sign27FirstCut.lift (drop u v) = v := by
  funext j
  fin_cases j <;> simp [drop, Sign27FirstCut.lift, hx, hy]

theorem drop_lift (v : Fin 28 → V) : drop (v 21) (Sign27FirstCut.lift v) = v := by
  funext j
  fin_cases j <;> simp [drop, Sign27FirstCut.lift]
end DiophantineConsistency.Sign27ZeroBridge
#print axioms DiophantineConsistency.Sign27ZeroBridge.lift_drop
#print axioms DiophantineConsistency.Sign27ZeroBridge.drop_lift
