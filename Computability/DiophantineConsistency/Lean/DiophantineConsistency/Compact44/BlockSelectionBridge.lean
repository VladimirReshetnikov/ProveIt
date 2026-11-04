import DiophantineConsistency.Compact44.OrbitDefinability
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace BlockSelectionBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactPartialBand
open CleanGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem selector_index (N h : V) (i : Fin 943) (hh : h<N) :
    cyc (8807*N) (8807*h+4393) (((4393-i.val):ℕ):V) = 8807*h+(i.val:V) := by
  have hiT : i.val≤4393 := by have := i.isLt; omega
  have hd : (((4393-i.val):ℕ):V)≤(4393:V) := by exact_mod_cast (Nat.sub_le 4393 i.val)
  have he := BlockCyclicIndex.reflected N h (4393:V) (((4393-i.val):ℕ):V) hh (by norm_num) hd
  have hsum : (i.val:V)+(((4393-i.val):ℕ):V)=(4393:V) := by exact_mod_cast (Nat.add_sub_of_le hiT)
  rw [(eq_tsub_of_add_eq hsum).symm] at he
  exact he

theorem selected_iff_digit (N C h : V) (hh : h<N)
    (hdec : UniformBandDecoder.Conclusion (8807*N) C (8807*h+4393) 4393) :
    FixedGraphOccupiedOrbit.SelectedBlock N C h ↔
      ∃ j<943, dig 67 C (8807*h+j)=1 := by
  constructor
  · rintro ⟨i,hi,hw⟩
    refine ⟨(i.val:V),by exact_mod_cast i.isLt,?_⟩
    have hbit := hi.1
    unfold selectorDigit at hbit
    rw [selector_index N h i hh] at hbit
    exact hbit
  · rintro ⟨j,hj,hbit⟩
    obtain ⟨m,hm,hmj⟩ := bounded_standard 943 j hj
    let i : Fin 943 := ⟨m,hm⟩
    have hi : selectorDigit (8807*N) C (8807*h+4393) 4393 i=1 := by
      unfold selectorDigit
      rw [selector_index N h i hh]
      simpa only [hmj] using hbit
    rcases hdec with hzero | hsel
    · have h := hzero.1 i
      rw [hi] at h
      exact False.elim (_root_.one_ne_zero h)
    · exact hsel
#print axioms BlockSelectionBridge.selector_index
#print axioms BlockSelectionBridge.selected_iff_digit
end BlockSelectionBridge
