import DiophantineConsistency.Source34.Source34Single
import DiophantineConsistency.Source34.Source34Flatten
import DiophantineConsistency.Mixed121.Mixed121KernelFiniteCert

/-! # Finite geometry of the source34 kernel terms

`Mixed121KernelFiniteCert` at the source34 tuple. The kernel
`Source34Kernel.paramKernel r` has the bare terms `r^40, r^41, r^1100, r^2200`,
two reflected bands `r^(4393−e)`, `r^(5495−e)` over the allowed positions `e`
(`Source34Single.Allowed`: the 943 selectors, the copy range `960..1038` and
the anchors), and `r^8801·r^1`.

* The two bands never meet (`1102` is not a difference of allowed positions),
  and neither meets a bare offset.
* Reflected exponents lie strictly inside `(0, 8801)`.
* The 44 extra positions are distinct and above the selectors.

Generic and used from `Mixed121KernelFiniteCert`: `band_injective` and the
radix bounds `clause_lt_radix`,
`copy_lt_radix`, `clause_lt_symbolic_radix`, `copy_lt_symbolic_radix`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34KernelFiniteCert
open Source34Kernel Source34Single
open scoped BigOperators

theorem cross_bands (e f : ℕ) (he : Allowed e) (hf : Allowed f) :
    4393-e ≠ 5495-f := by
  unfold Allowed at he hf
  omega

theorem bare_disjoint (e b : ℕ) (he : Allowed e) (hb : b=40 ∨ b=41 ∨ b=1100 ∨ b=2200) :
    4393-e≠b ∧ 5495-e≠b := by
  unfold Allowed at he
  omega

theorem selector_allowed (i : Fin 943) : Allowed i.val := by
  unfold Allowed
  exact Or.inl i.isLt

theorem extra_mem (k : Fin 44) : extraPos k ∈ extraPositions := List.get_mem extraPositions _

theorem extra_allowed (k : Fin 44) : Allowed (extraPos k) := copy_allowed k

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

theorem reflected_range (e : ℕ) (he : Allowed e) :
    0<4393-e ∧ 4393-e<8801 ∧ 0<5495-e ∧ 5495-e<8801 := by
  unfold Allowed at he
  omega

#print axioms Source34KernelFiniteCert.cross_bands
#print axioms Source34KernelFiniteCert.bare_disjoint
#print axioms Source34KernelFiniteCert.extra_allowed
#print axioms Source34KernelFiniteCert.copy_not_selector
#print axioms Source34KernelFiniteCert.copy_injective
#print axioms Source34KernelFiniteCert.reflected_range
end Source34KernelFiniteCert
