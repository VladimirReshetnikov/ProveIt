import DiophantineConsistency.Compact44.FixedGraphSingleBand
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SelectedBandInputs
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
open CompactSymbolicKernel CompactPartialBand
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_index (n : V) (T j : ℕ) (ht : (T:V)<n) (hj : j≤T) :
    cyc n (T:V) (((T-j):ℕ):V)=(j:V) := by
  have hsum : (j:V)+(((T-j):ℕ):V)=(T:V) := by
    exact_mod_cast (Nat.add_sub_of_le hj)
  have hle : (((T-j):ℕ):V)≤(T:V) := by
    rw [←hsum]
    exact le_add_of_nonneg_left (by simp)
  have hoff : (((T-j):ℕ):V)<n := lt_of_le_of_lt hle ht
  rw [cyc_of_le ht hoff hle]
  exact (eq_tsub_of_add_eq hsum).symm

theorem selected_inputs (n C : V) (T : ℕ) (ht : (T:V)<n) (hT : 3296≤T)
    (hbool : ∀ k<n, k%8807≠1063 → dig 67 C k≤1) :
    (∀ j : Fin 943, selectorDigit n C (T:V) T j≤1) ∧
    (∀ j : Fin 41, copyDigit position n C (T:V) T j≤1) := by
  constructor
  · intro j
    have hjT : j.val≤T := le_trans (by have := j.isLt; omega) hT
    have hj8807 : (j.val:V)<8807 := by exact_mod_cast (show j.val<8807 by have := j.isLt; omega)
    have hjn : (j.val:V)<n := lt_of_le_of_lt (by exact_mod_cast hjT) ht
    have hjsp : (j.val:V)≠1063 := by
      intro he
      have he' : j.val=1063 := by exact_mod_cast he
      have := j.isLt
      omega
    unfold selectorDigit
    rw [source_index n T j.val ht hjT]
    apply hbool _ hjn
    rwa [mod_eq_self_of_lt hj8807]
  · intro j
    have hall := ForeignBandGeometry.copy_allowed j
    unfold ForeignBandGeometry.Allowed at hall
    have hbound : position j≤3296 := by omega
    have hjT : position j≤T := le_trans hbound hT
    have hj8807 : (position j:V)<8807 := by exact_mod_cast (show position j<8807 by omega)
    have hjn : (position j:V)<n := lt_of_le_of_lt (by exact_mod_cast hjT) ht
    have hjsp : (position j:V)≠1063 := by
      intro he
      have he' : position j=1063 := by exact_mod_cast he
      omega
    unfold copyDigit
    rw [source_index n T (position j) ht hjT]
    apply hbool _ hjn
    rwa [mod_eq_self_of_lt hj8807]
#print axioms SelectedBandInputs.source_index
#print axioms SelectedBandInputs.selected_inputs
end SelectedBandInputs
