import DiophantineConsistency.ArithmeticWindowDigits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSelector
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticBinaryCarry
open DiophantineConsistency.ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The compact44 low mask forces at most one selector, even when the
payload contributes carries above the low selector limb. -/
theorem selector_at_most_one (n P : V) (hn : n<Exp.exp 10)
    (h : NoCarry (n+Exp.exp 10*P) (Exp.exp 51-2)) : n≤1 := by
  let S : V := n+Exp.exp 10*P
  have hm : Exp.exp 51-2<Exp.exp (51:V) := tsub_lt_self (exp_pos _) (by norm_num)
  have hd := noCarry_dig (51:V) S (Exp.exp 51-2) 0 h
  simp only [dig_zero_index,mod_eq_self_of_lt hm] at hd
  have hlow : S%Exp.exp 51≤1 := by
    apply noCarry_ones_two 50
    · simpa only [show (50:V)+1=51 by norm_num] using mod_lt S (exp_pos (51:V))
    · simpa only [show (50:V)+1=51 by norm_num] using hd
  have hmod : S%Exp.exp 51%Exp.exp 10=S%Exp.exp 10 := by
    simpa only [one_mul] using mod_mod_of_le (1:V) S 10 51 (by norm_num)
  have hS : S%Exp.exp 10=n := by
    dsimp [S]
    rw [mod_add_mul' _ _ (exp_pos (10:V)),mod_eq_self_of_lt hn]
  calc
    n=S%Exp.exp 10 := hS.symm
    _=S%Exp.exp 51%Exp.exp 10 := hmod.symm
    _≤S%Exp.exp 51 := mod_le _ _
    _≤1 := hlow
end CompactSelector
#print axioms CompactSelector.selector_at_most_one
