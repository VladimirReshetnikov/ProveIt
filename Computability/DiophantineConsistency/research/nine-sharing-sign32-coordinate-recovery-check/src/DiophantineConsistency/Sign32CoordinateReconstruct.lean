import DiophantineConsistency.Sign32CoordinateRecover

/-! UNCOMPILED: restore the old valuation by drop then lift. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32CoordinateRecover
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def drop {S : Type*} (v : Fin 34 → S) : Fin 33 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25, v 26, v 27, v 28, v 29, v 30, v 31, v 32, v 33]

theorem lift_drop (p : Fin 4 → ℤ) (beta : V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed33.seed p) v) :
    Sign32Substitution00.lift beta (drop v) = v := by
  have hq := q2_coordinate p beta v hp0 hz
  funext j
  fin_cases j <;> simp [Sign32Substitution00.lift, drop, hq]
end DiophantineConsistency.Sign32CoordinateRecover
#print axioms DiophantineConsistency.Sign32CoordinateRecover.lift_drop
