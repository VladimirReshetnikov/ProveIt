import DiophantineConsistency.Mixed121.Mixed121Single
import DiophantineConsistency.Mixed121.Mixed121Flatten

/-! # Finite geometry of the 121x8801 kernel terms

The 121x8801 counterpart of Compact44's `CompactKernelFiniteCert`. The kernel
`paramKernel r` has the bare terms `r^30, r^62, r^1100, r^2200`, two reflected
bands `r^(4393−e)`, `r^(5495−e)` over the allowed positions `e`
(`Mixed121Single.Allowed`: the 943 selectors, the copy cells `983..1032` and
the anchors `1095, 1096, 2195, 3296`), and `r^8801·r^42`.

* The two bands never meet, and neither meets a bare offset.
* Reflected exponents lie strictly inside `(0, 8801)`.
* The 44 extra positions are distinct and above the selectors.
* Every clause coefficient and every extra weight is below `2^121`, hence
  below any radix `r ≥ 2^121`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121KernelFiniteCert
open Mixed121Kernel Mixed121Single
open scoped BigOperators

theorem cross_bands (e f : ℕ) (he : Allowed e) (hf : Allowed f) :
    4393-e ≠ 5495-f := by
  unfold Allowed at he hf
  omega

theorem bare_disjoint (e b : ℕ) (he : Allowed e) (hb : b=30 ∨ b=62 ∨ b=1100 ∨ b=2200) :
    4393-e≠b ∧ 5495-e≠b := by
  unfold Allowed at he
  omega

theorem band_injective (T e f : ℕ) (he : e≤T) (hf : f≤T) (h : T-e=T-f) : e=f := by omega

theorem selector_allowed (i : Fin 943) : Allowed i.val := by
  unfold Allowed
  exact Or.inl i.isLt

theorem extra_mem (k : Fin 44) : extraPos k ∈ extraPositions := List.get_mem extraPositions _

theorem extra_allowed (k : Fin 44) : Allowed (extraPos k) := by
  have hm := extra_mem k
  simp only [extraPositions, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hm
  unfold Allowed
  rcases hm with ((((⟨a, ha, h⟩ | ⟨a, ha, h⟩) | ⟨a, ha, h⟩) | ⟨a, ha, h⟩) | h | h | h | h) <;> omega

theorem copy_not_selector (k : Fin 44) : 943≤extraPos k := by
  have hm := extra_mem k
  simp only [extraPositions, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hm
  rcases hm with ((((⟨a, ha, h⟩ | ⟨a, ha, h⟩) | ⟨a, ha, h⟩) | ⟨a, ha, h⟩) | h | h | h | h) <;> omega

theorem extras_nodup : extraPositions.Nodup := by decide

theorem copy_injective : Function.Injective extraPos := by
  intro i j h
  apply Fin.ext
  have he := (List.nodup_iff_injective_get.mp extras_nodup) h
  exact congrArg Fin.val he

theorem clause_lt_radix (i : Fin 943) : clause (Compact943Data.row i) < 2^121 :=
  lt_trans (Mixed121Flatten.clause_lt _) (Nat.pow_lt_pow_right (by decide) (by decide))

theorem copy_lt_radix (k : Fin 44) : W k.val < 2^121 :=
  lt_trans (Mixed121Flatten.W_lt k.val k.isLt) (Nat.pow_lt_pow_right (by decide) (by decide))

theorem reflected_range (e : ℕ) (he : Allowed e) :
    0<4393-e ∧ 4393-e<8801 ∧ 0<5495-e ∧ 5495-e<8801 := by
  unfold Allowed at he
  omega

theorem clause_lt_symbolic_radix (r : ℕ) (hr : 2^121≤r) (i : Fin 943) :
    clause (Compact943Data.row i)<r :=
  lt_of_lt_of_le (clause_lt_radix i) hr

theorem copy_lt_symbolic_radix (r : ℕ) (hr : 2^121≤r) (k : Fin 44) :
    W k.val<r := lt_of_lt_of_le (copy_lt_radix k) hr

#print axioms Mixed121KernelFiniteCert.cross_bands
#print axioms Mixed121KernelFiniteCert.bare_disjoint
#print axioms Mixed121KernelFiniteCert.extra_allowed
#print axioms Mixed121KernelFiniteCert.copy_not_selector
#print axioms Mixed121KernelFiniteCert.copy_injective
#print axioms Mixed121KernelFiniteCert.clause_lt_symbolic_radix
#print axioms Mixed121KernelFiniteCert.copy_lt_symbolic_radix
#print axioms Mixed121KernelFiniteCert.reflected_range
end Mixed121KernelFiniteCert
