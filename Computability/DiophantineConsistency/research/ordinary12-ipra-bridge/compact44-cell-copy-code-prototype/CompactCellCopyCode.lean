import DiophantineConsistency.CompactWordCellClient
import DiophantineConsistency.ForeignBandGeometry

/-! Construct an inverse of the compact44 payload-slot map, without a
full 8,807-entry model table. Slot codes are one-based; zero means absent. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace CompactCellCopyCode
open DiophantineConsistency
open DiophantineConsistency.ArithmeticWangTable
open CompactSymbolicKernel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The inverse indices for the contiguous positions 983 through 1031. -/
def nearCodes : List ℕ := [26,27,28,29,30,31,32,33,34,38,0,0,0,0,0,0,0,0,0,0,
  18,19,20,21,22,23,24,25,37,0,9,10,11,12,13,14,15,16,17,36,1,2,3,4,5,6,7,8,35]

def copyCode (k : V) : V :=
  if k = 1095 then 39 else if k = 2195 then 40 else if k = 3296 then 41
  else if 983 ≤ k then tabValue nearCodes 0 (k-983) else 0

instance near_table_definable : 𝚺₁-Function₁[V] (tabValue nearCodes 0) :=
  (tab_defined nearCodes 0).to_definable.of_zero

theorem copyCode_definable : 𝚺₁-Function₁[V] copyCode := by
  have hR : 𝚺₁.Definable (fun v : Fin 2 → V =>
    (v 1=1095 ∧ v 0=39) ∨
    (v 1≠1095 ∧ v 1=2195 ∧ v 0=40) ∨
    (v 1≠1095 ∧ v 1≠2195 ∧ v 1=3296 ∧ v 0=41) ∨
    (v 1≠1095 ∧ v 1≠2195 ∧ v 1≠3296 ∧ 983≤v 1 ∧
      v 0=tabValue nearCodes 0 (v 1-983)) ∨
    (v 1≠1095 ∧ v 1≠2195 ∧ v 1≠3296 ∧ v 1<983 ∧ v 0=0)) := by definability
  apply hR.of_iff
  intro v
  unfold copyCode
  by_cases h1 : v 1=1095 <;> by_cases h2 : v 1=2195 <;>
    by_cases h3 : v 1=3296 <;> by_cases h4 : 983≤v 1 <;> simp [h1,h2,h3,h4,not_le.mp,not_lt.mpr]

/-- Selectors and the dummy position cannot be mistaken for copy slots. -/
theorem below_copy (k : V) (hk : k<943) : copyCode k=0 := by
  unfold copyCode
  have h1 : k≠1095 := ne_of_lt (lt_trans hk (by norm_num))
  have h2 : k≠2195 := ne_of_lt (lt_trans hk (by norm_num))
  have h3 : k≠3296 := ne_of_lt (lt_trans hk (by norm_num))
  have h4 : ¬983≤k := not_le_of_gt (lt_trans hk (by norm_num))
  simp [h1,h2,h3,h4]

theorem at_dummy : copyCode (1063 : V)=0 := by
  unfold copyCode
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num)]
  have ht : (1063 : V)-983 = 80 := tsub_eq_of_eq_add (by norm_num)
  rw [ht, show (80:V)=((80:ℕ):V) by simp, tab_cast]
  norm_num [nearCodes]

/-- Standard subtraction transported to the model when the subtrahend fits. -/
theorem numeral_sub (a b : ℕ) (h : b ≤ a) :
    (a : V) - (b : V) = ((a - b : ℕ) : V) := by
  apply tsub_eq_of_eq_add
  exact_mod_cast (Nat.sub_add_cancel h).symm

/-- Compute the lookup on standard inputs in ℕ before casting into the model. -/
theorem copyCode_cast (n : ℕ) : copyCode (n : V) =
    ((if n = 1095 then 39 else if n = 2195 then 40 else if n = 3296 then 41
      else if 983 ≤ n then nearCodes.getD (n - 983) 0 else 0 : ℕ) : V) := by
  by_cases h1 : n = 1095
  · subst n; simp [copyCode]
  by_cases h2 : n = 2195
  · subst n; simp [copyCode]
  by_cases h3 : n = 3296
  · subst n; simp [copyCode]
  have hv1 : (n : V) ≠ 1095 := by exact_mod_cast h1
  have hv2 : (n : V) ≠ 2195 := by exact_mod_cast h2
  have hv3 : (n : V) ≠ 3296 := by exact_mod_cast h3
  by_cases h4 : 983 ≤ n
  · have hv4 : (983 : V) ≤ (n : V) := by exact_mod_cast h4
    simp only [copyCode, hv1, hv2, hv3, hv4, h1, h2, h3, h4, if_false, if_true]
    rw [show (983 : V) = ((983 : ℕ) : V) by simp, numeral_sub n 983 h4, tab_cast]
  · have hv4 : ¬ (983 : V) ≤ (n : V) := by exact_mod_cast h4
    simp [copyCode, hv1, hv2, hv3, hv4, h1, h2, h3, h4]

/-- Every actual payload slot maps back to its one-based payload bit. -/
theorem at_slot (i : Fin 41) : copyCode (position i:V) = (i.val+1:ℕ) := by
  rw [copyCode_cast]
  congr 1
  fin_cases i <;> decide

#print axioms CompactCellCopyCode.copyCode_definable
#print axioms CompactCellCopyCode.below_copy
#print axioms CompactCellCopyCode.at_dummy
#print axioms CompactCellCopyCode.at_slot
end CompactCellCopyCode
