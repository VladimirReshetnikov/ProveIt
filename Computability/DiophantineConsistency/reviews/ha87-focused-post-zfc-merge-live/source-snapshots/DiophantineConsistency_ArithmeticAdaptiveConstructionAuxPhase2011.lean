import DiophantineConsistency.ArithmeticAdaptiveConstructionAuxClient2011
import DiophantineConsistency.ArithmeticPellRecurrence

/-! The auxiliary Pell seed has a nontrivial ordinate in the required phase. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionAuxPhase2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The phase `R % 4 = 3` makes the Pell ordinate at index R at least two,
for an arbitrary internal Pell parameter. -/
theorem ordinate_bound (R b : V) (hphase : R%4=3) : 2≤ycoord R b := by
  have hR : (3:V)≤R := by simpa only [hphase] using mod_le R 4
  exact le_trans (by norm_num : (2:V)≤3) (le_trans hR (time_le_y R b))
end DiophantineConsistency.ArithmeticAdaptiveConstructionAuxPhase2011
