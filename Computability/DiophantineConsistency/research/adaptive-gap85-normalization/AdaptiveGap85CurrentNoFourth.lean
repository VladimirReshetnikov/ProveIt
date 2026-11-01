import DiophantineConsistency.AdaptiveGap85NoFourthLargeQ
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85CurrentNoFourth
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticPellRecurrence
open AdaptiveGap85Literal AdaptiveGap85NoFourthLargeQ ArithmeticAdaptiveScaledNorms2011
attribute [local irreducible] CurrentMasks2011.radix
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The literal first-port constant is at least four in every IΣ₁ model. -/
theorem current_first_port_four : (4:V)≤(currentPorts 0:V) := by
  have hr : 5≤CurrentMasks2011.radix := by norm_num [CurrentMasks2011.radix]
  have hp : CurrentMasks2011.radix≤CurrentMasks2011.radix^2011 := Nat.le_pow (a := CurrentMasks2011.radix) (b := 2011) (by decide)
  have hb : 4≤CurrentMasks2011.beta := by
    unfold CurrentMasks2011.beta
    exact Nat.le_sub_of_add_le (by simpa only [show 4+1=5 by decide] using le_trans hr hp)
  have hc : 4≤currentPorts 0 := by
    change 4≤CurrentMasks2011.beta
    exact hb
  exact_mod_cast hc

theorem current_q_five (v : Fin 13 → V) (hv0 : 0<v 0) : 5≤1+v 0*(currentPorts 0:V) := by
  have hj : 1≤v 0 := pos_iff_one_le.mp hv0
  have hm : (currentPorts 0:V)≤v 0*(currentPorts 0:V) := by
    simpa only [one_mul] using Arithmetic.mul_le_mul_right (a:=(currentPorts 0:V)) hj
  calc
    _ = 1+4 := by ring
    _ ≤ 1+(currentPorts 0:V) := add_le_add (le_refl _) current_first_port_four
    _ ≤ _ := add_le_add (le_refl _) hm

/-- An actual positive zero for the literal fixed ports cannot have fourth
main Pell ordinate. Higher indices and global zero existence remain open. -/
theorem current_zero_not_fourth_main (v : Fin 13 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (currentPorts j:ℤ))) v) :
    v 9+v 7*(v 9+v 10) ≠ ycoord 4 (v 6*v 7+v 7) := by
  have hb : 0<(currentPorts 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<4) current_first_port_four
  exact actual_zero_not_fourth_main_of_large_q currentPorts v hb hv hz (current_q_five v (hv 0))
end DiophantineConsistency.AdaptiveGap85CurrentNoFourth
