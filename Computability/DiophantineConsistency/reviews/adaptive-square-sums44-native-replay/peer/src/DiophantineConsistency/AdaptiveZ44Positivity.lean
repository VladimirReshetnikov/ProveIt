import DiophantineConsistency.ArithmeticAdaptiveTransport2011
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 3000000
noncomputable section
namespace DiophantineConsistency.AdaptiveZ44Positivity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticAdaptiveTransport2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A positive root with the first norm cannot exceed its offset by a natural term. -/
theorem impossible_nonpositive (s ell k r t extra : V)
    (hs : 0 < s) (he : 0 < ell) (hk : 0 < k)
    (hn : t*t = 1 + ell*(ell+k))
    (hroot : s*t = s*(ell+k+r)+extra) : False := by
  have ht := first_root_bound ell k t he hk hn
  have hlt : s*t < s*(ell+k) := mul_lt_mul_of_pos_left ht hs
  have hle : s*(ell+k) ≤ s*t := calc
    _ ≤ s*(ell+k+r) := mul_le_mul_of_nonneg_left (by simp) (Arithmetic.zero_le _)
    _ ≤ s*(ell+k+r)+extra := by simp
    _ = s*t := hroot.symm
  exact (not_lt_of_ge hle) hlt
#print axioms impossible_nonpositive
end DiophantineConsistency.AdaptiveZ44Positivity
