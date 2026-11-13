import DiophantineConsistency.Compact44.CompactSelector
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSelectorDiv
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticBinaryCarry
open DiophantineConsistency.ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem selector_payload_divisible (n P : V) (hn : n<Exp.exp 10)
    (h : NoCarry (n+Exp.exp 10*P) (Exp.exp 51-2)) :
    n≤1 ∧ Exp.exp 41∣P := by
  let S : V := n+Exp.exp 10*P
  have hcount : n≤1 := CompactSelector.selector_at_most_one n P hn h
  have hm : Exp.exp 51-2<Exp.exp (51:V) := tsub_lt_self (exp_pos _) (by norm_num)
  have hd := noCarry_dig (51:V) S (Exp.exp 51-2) 0 h
  simp only [dig_zero_index,mod_eq_self_of_lt hm] at hd
  have hlow : S%Exp.exp 51≤1 := by
    apply noCarry_ones_two 50
    · simpa only [show (50:V)+1=51 by norm_num] using mod_lt S (exp_pos (51:V))
    · simpa only [show (50:V)+1=51 by norm_num] using hd
  have hS : S%Exp.exp 10=n := by
    dsimp [S]
    rw [mod_add_mul' _ _ (exp_pos (10:V)),mod_eq_self_of_lt hn]
  have hquot : S/Exp.exp 10=P := by
    dsimp [S]
    rw [show n+Exp.exp 10*P=P*Exp.exp 10+n by ring,div_mul_add _ _ hn]
  have hsplit : S%Exp.exp 51=n+(P%Exp.exp 41)*Exp.exp 10 := by
    have hs := mod_mul_split S (Exp.exp 10) (Exp.exp 41) (exp_pos _) (exp_pos _)
    rw [←exp_add,show (10:V)+41=51 by norm_num,hS,hquot] at hs
    exact hs
  have hten : (1:V)<Exp.exp 10 := by
    have he : (2:V)≤Exp.exp 10 := by
      simpa only [exp_one] using (exp_monotone_le.mpr (by norm_num : (1:V)≤10))
    exact lt_of_lt_of_le (by norm_num : (1:V)<2) he
  have hz : P%Exp.exp 41=0 := by
    by_contra hnz
    have hp : 1≤P%Exp.exp 41 := pos_iff_one_le.mp (pos_iff_ne_zero.mpr hnz)
    have he : Exp.exp 10≤(P%Exp.exp 41)*Exp.exp 10 :=
      le_mul_of_one_le_left (by simp) hp
    have he' : (P%Exp.exp 41)*Exp.exp 10≤S%Exp.exp 51 := by rw [hsplit]; simp
    exact (not_le_of_gt hten) (le_trans he (le_trans he' hlow))
  exact ⟨hcount,mod_eq_zero_iff_dvd.mp hz⟩
end CompactSelectorDiv
#print axioms CompactSelectorDiv.selector_payload_divisible
