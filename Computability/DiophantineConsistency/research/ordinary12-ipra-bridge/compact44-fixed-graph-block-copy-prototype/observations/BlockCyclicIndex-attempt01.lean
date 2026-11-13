import DiophantineConsistency.FixedGraphParityCopy
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace BlockCyclicIndex
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem reflected (N h j d : V) (hh : h<N) (hj : j<8807) (hd : d≤j) :
    cyc (8807*N) (8807*h+j) d = 8807*h+(j-d) := by
  have hk : 8807*h+j<8807*N := (CompactSelectorPeriod.period_index_zero_allowed N h j hh hj).1
  have hdlt : d<8807*N := lt_of_le_of_lt hd (lt_of_le_of_lt (le_add_of_nonneg_left (by simp)) hk)
  have hdk : d≤8807*h+j := le_trans hd (le_add_of_nonneg_left (by simp))
  rw [cyc_of_le hk hdlt hdk]
  apply (eq_tsub_of_add_eq ?_).symm
  rw [add_assoc,tsub_add_cancel_of_le hd]

theorem shift (N h s j : V) (hN : 0<N) (hh : h<N) (hs : s<N) (hj : j<8807) :
    cyc (8807*N) (8807*h+j) (8807*s) = 8807*(cyc N h s)+j := by
  have hk : 8807*h+j<8807*N := (CompactSelectorPeriod.period_index_zero_allowed N h j hh hj).1
  have he : 8807*s<8807*N := mul_lt_mul_of_pos_left hs (by norm_num)
  by_cases hsh : s≤h
  · have hle : 8807*s≤8807*h+j := le_trans (mul_le_mul_of_nonneg_left hsh (by norm_num)) (le_add_of_nonneg_right (by simp))
    rw [cyc_of_le hk he hle,cyc_of_le hh hs hsh]
    apply (eq_tsub_of_add_eq ?_).symm
    rw [←add_assoc,←mul_add,tsub_add_cancel_of_le hsh]
  · have hhs : h<s := lt_of_not_ge hsh
    have hlt : 8807*h+j<8807*s := calc
      _ < 8807*h+8807 := add_lt_add_right hj _
      _ = 8807*(h+1) := by ring
      _ ≤ 8807*s := mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp hhs) (by norm_num)
    rw [cyc_of_lt he hlt,cyc_of_lt hs hhs]
    rw [mul_add, add_assoc]
    congr 1
    exact (mul_tsub (8807:V) N s).symm
#print axioms BlockCyclicIndex.reflected
#print axioms BlockCyclicIndex.shift
end BlockCyclicIndex
