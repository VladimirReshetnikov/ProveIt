import DiophantineConsistency.ForeignBandGeometry
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactKernelFiniteCert
open CompactSymbolicKernel ForeignBandGeometry
open scoped BigOperators

theorem cross_bands (e f : ℕ) (he : Allowed e) (hf : Allowed f) :
    4393-e ≠ 5495-f := by
  unfold Allowed at he hf
  omega

theorem bare_disjoint (e b : ℕ) (he : Allowed e) (hb : b=30 ∨ b=62 ∨ b=1100 ∨ b=2201) :
    4393-e≠b ∧ 5495-e≠b := by
  unfold Allowed at he
  omega

theorem band_injective (T e f : ℕ) (he : e≤T) (hf : f≤T) (h : T-e=T-f) : e=f := by omega

theorem selector_allowed (i : Fin 943) : Allowed i.val := by
  unfold Allowed
  exact Or.inl i.isLt

theorem copy_not_selector (j : Fin 41) : 943≤position j := by
  have hm : position j ∈ slots := List.get_mem slots _
  simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

theorem slots_nodup : slots.Nodup := by decide

theorem copy_injective : Function.Injective position := by
  intro i j h
  apply Fin.ext
  have he := (List.nodup_iff_injective_get.mp slots_nodup) h
  exact congrArg Fin.val he

theorem selector_lt_radix (i : Fin 943) :
    CompactCoefficientMass.selector (Compact943Data.row i)<2^67 := by
  unfold CompactCoefficientMass.selector
  have hh := Nat.sub_le (2^41) (CompactCoefficientMass.value (Compact943Data.row i))
  norm_num only [show 2^10=1024 by decide, show 2^41=2199023255552 by decide,
    show 2^67=147573952589676412928 by decide] at *
  omega

theorem copy_lt_radix (j : Fin 41) : 2^(10+j.val)<2^67 := by
  apply Nat.pow_lt_pow_right (by decide : 1<2)
  have hj := j.isLt
  omega

theorem reflected_range (e : ℕ) (he : Allowed e) :
    0<4393-e ∧ 4393-e<8807 ∧ 0<5495-e ∧ 5495-e<8807 := by
  unfold Allowed at he
  omega

theorem selector_lt_symbolic_radix (r : ℕ) (hr : 2^67≤r) (i : Fin 943) :
    CompactCoefficientMass.selector (Compact943Data.row i)<r :=
  lt_of_lt_of_le (selector_lt_radix i) hr

theorem copy_lt_symbolic_radix (r : ℕ) (hr : 2^67≤r) (j : Fin 41) :
    2^(10+j.val)<r := lt_of_lt_of_le (copy_lt_radix j) hr

#print axioms CompactKernelFiniteCert.reflected_range
#print axioms CompactKernelFiniteCert.selector_lt_symbolic_radix
#print axioms CompactKernelFiniteCert.copy_lt_symbolic_radix
#print axioms CompactKernelFiniteCert.cross_bands
#print axioms CompactKernelFiniteCert.bare_disjoint
#print axioms CompactKernelFiniteCert.band_injective
#print axioms CompactKernelFiniteCert.copy_not_selector
#print axioms CompactKernelFiniteCert.copy_injective
#print axioms CompactKernelFiniteCert.selector_lt_radix
#print axioms CompactKernelFiniteCert.copy_lt_radix
end CompactKernelFiniteCert
