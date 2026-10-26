import DiophantineConsistency.CurrentPhaseParity2011
import DiophantineConsistency.NativeWindowCarry

/-! Focused checks bind the marker proof to the actual source temporal digits.
The physical one-selector premise remains explicit; no tile or consistency
equivalence is used to prove fractional alignment. -/

namespace DiophantineConsistency.CurrentPhaseParity2011Checks

open NativeCyclicConvolution CurrentMasks2011 CurrentPhaseParity2011
open scoped BigOperators

set_option Elab.async false

variable {N : ℕ} [NeZero (N * 2011)]

example : CurrentHighDigits2011.maskDigits (1004 : ZMod (N * 2011)) = 1 := by
  simpa only [zero_add] using marker_mask (0 : ZMod (N * 2011)) (by simp)

example (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0) :
    convolution CurrentKernel2011.folded c 1004 =
      c 0 + CurrentReflectedGeometry2011.reflected c 1004 := by
  simpa only [zero_add] using marker_convolution c hsupport 0 (by simp)

example (x : Fin 31 → ℕ) (c carry digits : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (h0 : c 0 = 1)
    (hk : ∀ k, carry k ≤ 57)
    (hrec : ∀ k, carry k =
      (convolution CurrentKernel2011.folded c k + NativeWindowCarry.temporalDigits 47 x c k +
        carry (k - 1)) / radix)
    (hlocal : ∀ k, convolution CurrentKernel2011.folded c k +
      NativeWindowCarry.temporalDigits 47 x c k + carry (k - 1) = digits k + radix * carry k)
    (hm : ∀ k, digits k &&& CurrentHighDigits2011.maskDigits k = 0)
    (hone : (∑ f : Fin 942, c (f.val : ZMod (N * 2011))) ≤ 1) :
    ((NativePellBootstrap.nativeRank x).toNat - 47 * (N * 2011)) % 47 = 0 := by
  exact fractional_phase_zero _ c carry digits hc hsupport h0 hk hrec hlocal hm hone

#print axioms marker_target_residue
#print axioms marker_mask
#print axioms marker_convolution
#print axioms marker_digit_even
#print axioms marker_digit_parity
#print axioms origin_zero_of_fractional_phase
#print axioms fractional_phase_zero

end DiophantineConsistency.CurrentPhaseParity2011Checks
