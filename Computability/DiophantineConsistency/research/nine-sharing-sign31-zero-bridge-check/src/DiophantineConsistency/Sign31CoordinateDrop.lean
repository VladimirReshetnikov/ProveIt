import DiophantineConsistency.Sign31CoordinateRecover

/-! UNCOMPILED: restore the old valuation by drop then lift. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign31CoordinateRecover
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def drop {S : Type*} (v : Fin 33 → S) : Fin 32 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25, v 26, v 28, v 29, v 30, v 31, v 32]

theorem lift_drop (p : Fin 4 → ℤ) (v : Fin 33 → V)
    (hz : InternalZero (SharingSeed32Sextic.seed p) v) :
    Sign31FirstCut.lift (drop v) = v := by
  have hf := f2_coordinate p v hz
  funext j
  fin_cases j <;> simp [Sign31FirstCut.lift, drop, hf]
end DiophantineConsistency.Sign31CoordinateRecover
#print axioms DiophantineConsistency.Sign31CoordinateRecover.lift_drop
