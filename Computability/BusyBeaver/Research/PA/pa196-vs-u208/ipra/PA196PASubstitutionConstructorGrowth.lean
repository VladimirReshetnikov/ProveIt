import DiophantineConsistency.PRAWitnessCodeGrowth

/-! Uniform local output bounds for the four recursive formula constructors.
These do not by themselves bound the recursive child outputs or stages. -/
set_option autoImplicit false
namespace PA196PASubstitutionConstructorGrowth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem and_le (B a b : V) (ha : a ≤ B) (hb : b ≤ B) :
    a ^⋏ b ≤ tau (B+8) (22*B+22) := by
  have ha' : a ≤ tau (B+8) 0 := le_trans ha (le_trans le_self_add (le_tau _ _))
  have hb' : b ≤ tau (B+8) 0 := le_trans hb (le_trans le_self_add (le_tau _ _))
  have ht : (4 : V) ≤ tau (B+8) 0 := four_le_tau _ _
  have hc := code3_le_tau ht ha' hb'
  apply le_trans (by simpa [qqAnd] using hc)
  exact tau_mono le_rfl (le_trans (by norm_num : (2:V)+2 ≤ 22) le_add_self)

theorem or_le (B a b : V) (ha : a ≤ B) (hb : b ≤ B) :
    a ^⋎ b ≤ tau (B+8) (22*B+22) := by
  have ha' : a ≤ tau (B+8) 0 := le_trans ha (le_trans le_self_add (le_tau _ _))
  have hb' : b ≤ tau (B+8) 0 := le_trans hb (le_trans le_self_add (le_tau _ _))
  have ht : (5 : V) ≤ tau (B+8) 0 :=
    le_trans (by norm_num : (5:V) ≤ 8) (le_trans le_add_self (le_tau _ _))
  have hc := code3_le_tau ht ha' hb'
  apply le_trans (by simpa [qqOr] using hc)
  exact tau_mono le_rfl (le_trans (by norm_num : (2:V)+2 ≤ 22) le_add_self)

theorem all_le (B a : V) (ha : a ≤ B) : ^∀ a ≤ tau (B+8) (22*B+22) := by
  have ha' : a ≤ tau (B+8) 0 := le_trans ha (le_trans le_self_add (le_tau _ _))
  have ht : (6 : V) ≤ tau (B+8) 0 :=
    le_trans (by norm_num : (6:V) ≤ 8) (le_trans le_add_self (le_tau _ _))
  have hc := code2_le_tau ht ha'
  apply le_trans (by simpa [qqAll] using hc)
  exact tau_mono le_rfl (le_trans (by norm_num : (2:V) ≤ 22) le_add_self)

theorem exs_le (B a : V) (ha : a ≤ B) : ^∃ a ≤ tau (B+8) (22*B+22) := by
  have ha' : a ≤ tau (B+8) 0 := le_trans ha (le_trans le_self_add (le_tau _ _))
  have ht : (7 : V) ≤ tau (B+8) 0 :=
    le_trans (by norm_num : (7:V) ≤ 8) (le_trans le_add_self (le_tau _ _))
  have hc := code2_le_tau ht ha'
  apply le_trans (by simpa [qqExs] using hc)
  exact tau_mono le_rfl (le_trans (by norm_num : (2:V) ≤ 22) le_add_self)

#print axioms and_le
#print axioms or_le
#print axioms all_le
#print axioms exs_le
end PA196PASubstitutionConstructorGrowth
