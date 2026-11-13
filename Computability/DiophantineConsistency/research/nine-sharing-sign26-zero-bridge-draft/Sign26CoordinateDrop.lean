import DiophantineConsistency.Sign26RemainingCuts01

/-! SOURCE-ONLY: coordinate identities for the gap lift. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def drop {S : Type*} (v : Fin 28 → S) : Fin 27 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 23, v 24, v 25, v 26, v 27]

theorem lift_drop (v : Fin 28 → V) : Sign26CongruenceCuts.lift (v 22) (drop v) = v := by
  funext j
  fin_cases j <;> simp [drop, Sign26CongruenceCuts.lift]

theorem drop_lift (gap : V) (v : Fin 27 → V) : drop (Sign26CongruenceCuts.lift gap v) = v := by
  funext j
  fin_cases j <;> simp [drop, Sign26CongruenceCuts.lift]
end DiophantineConsistency.Sign26ZeroBridge
#print axioms DiophantineConsistency.Sign26ZeroBridge.lift_drop
#print axioms DiophantineConsistency.Sign26ZeroBridge.drop_lift
