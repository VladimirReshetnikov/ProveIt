import DiophantineConsistency.Sign28CoordinateRecover

/-! UNCOMPILED: restore the old valuation by drop then lift. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign28CoordinateRecover
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def drop {S : Type*} (v : Fin 32 → S) : Fin 29 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 17, v 18, v 19, v 20, v 21, v 22, v 24, v 25, v 26, v 27, v 28, v 29, v 31]

theorem lift_drop (p : Fin 4 → ℤ) (beta : V) (v : Fin 32 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed31Sextic.seed p) v) :
    Sign28FirstCuts.lift beta (drop v) = v := by
  have hx := x_coordinate p beta v hp0 hz
  have hc := c2_coordinate p v hz
  have hs := s2_coordinate p v hz
  funext j
  fin_cases j <;> simp [Sign28FirstCuts.lift, drop, hx, hc, hs]
end DiophantineConsistency.Sign28CoordinateRecover
#print axioms DiophantineConsistency.Sign28CoordinateRecover.lift_drop
