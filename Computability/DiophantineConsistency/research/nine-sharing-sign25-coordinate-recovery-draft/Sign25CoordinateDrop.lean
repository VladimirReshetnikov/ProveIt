import DiophantineConsistency.Sign25CoordinateRecover

/-! SOURCE-ONLY: restore old valuation from its drop under old zero. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25CoordinateRecover
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def drop {S : Type*} (v : Fin 27 → S) : Fin 26 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 20, v 21, v 22, v 23, v 24, v 25, v 26]

theorem lift_drop (p : Fin 4 → ℤ) (v : Fin 27 → V)
    (hz : InternalZero (SharingSeed26Sextic.seed p) v) :
    Sign25FirstCut.lift (drop v) = v := by
  have he := ell_coordinate p v hz
  funext j
  fin_cases j <;> simp [Sign25FirstCut.lift, drop, he]
end DiophantineConsistency.Sign25CoordinateRecover
#print axioms DiophantineConsistency.Sign25CoordinateRecover.lift_drop
