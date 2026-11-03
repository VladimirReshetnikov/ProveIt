import CompactKernelSplit
import KernelTermBounds

/-! A deliberately coarse finite mass bound, sufficient for high padding. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactLowerKernelMass
open CompactKernelSplit CompactSymbolicKernel CompactSymbolicKernelOpaque ConcreteSparseKernel TopDigit
attribute [local irreducible] paramKernel rho lowTerms kernelTerms

theorem weighted_bound (r : ℕ) (hr : 1 ≤ r) (ts : List (ℕ × ℕ))
    (hpos : ∀ t ∈ ts, t.1 ≤ 5495)
    (hweight : ∀ t ∈ ts, t.2 ≤ 2^51+1) :
    (ts.map (fun t => t.2 * r ^ t.1)).sum ≤
      ts.length * ((2^51+1) * r^5495) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have hp : t.1 ≤ 5495 := hpos t (by simp)
    have hw : t.2 ≤ 2^51+1 := hweight t (by simp)
    have hps : ∀ u ∈ ts, u.1 ≤ 5495 := fun u hu => hpos u (by simp [hu])
    have hws : ∀ u ∈ ts, u.2 ≤ 2^51+1 := fun u hu => hweight u (by simp [hu])
    have hpow : r ^ t.1 ≤ r ^ 5495 := Nat.pow_le_pow_right (by omega) hp
    have ht := Nat.mul_le_mul hw hpow
    have hs := ih hps hws
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem low_length : lowTerms.length ≤ 1973 := by
  have hk : kernelTerms = lowTerms ++ [(8849,1)] := by rfl
  have hl := KernelTermBounds.kernel_terms_length
  rw [hk] at hl
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  omega

/-- Coefficient mass is bounded by 2^62, without expanding the row table. -/
theorem lower_le (r : ℕ) (hr : 1 ≤ r) : lowerKernelAt r ≤ 2^62 * r^5495 := by
  unfold lowerKernelAt
  have hp : ∀ t ∈ lowTerms, t.1 ≤ 5495 := by
    intro t ht
    have hh := lowTerms_lt t ht
    omega
  have hw : ∀ t ∈ lowTerms, t.2 ≤ 2^51+1 := by
    intro t ht
    apply KernelTermBounds.kernel_weights_bound t
    have hk : kernelTerms = lowTerms ++ [(8849,1)] := by rfl
    rw [hk]
    exact List.mem_append_left _ ht
  have h := weighted_bound r hr lowTerms hp hw
  calc
    _ ≤ lowTerms.length * ((2^51+1) * r^5495) := h
    _ ≤ 1973 * ((2^51+1) * r^5495) := Nat.mul_le_mul_right _ low_length
    _ = (1973 * (2^51+1)) * r^5495 := by ring
    _ ≤ 2^62 * r^5495 := Nat.mul_le_mul_right _ (by norm_num)

#print axioms CompactLowerKernelMass.weighted_bound
#print axioms CompactLowerKernelMass.low_length
#print axioms CompactLowerKernelMass.lower_le
end CompactLowerKernelMass
