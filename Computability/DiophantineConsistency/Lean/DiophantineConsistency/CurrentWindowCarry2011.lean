import DiophantineConsistency.CurrentKernelData2011
import DiophantineConsistency.CurrentKernel2011
import DiophantineConsistency.NativeWindowCarry

/-! The complete fixed2011 ports discharge the source-window numerical interface. -/
namespace DiophantineConsistency.CurrentWindowCarry2011
open NativeCyclicConvolution CurrentKernel2011
set_option Elab.async false
variable {n : ℕ} [NeZero n]

theorem interface : NativeSourceMask.Interface ports CurrentMasks2011.width
    CurrentMasks2011.lowPort CurrentMasks2011.highPort :=
  CurrentMasks2011.interface (K : ℤ) (Nat.cast_nonneg K)

/-- The fixed kernel and masks discharge the generic arithmetic carry budget.
The remaining word bindings are explicit; no tableau calibration is assumed. -/
theorem source_carries (x : Fin 31 → ℕ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, SplitCertificate59.sourceRows ports (fun k => (x k : ℤ)) j = 0)
    (c m : ZMod n → ℕ) (hc : ∀ i, c i ≤ 1) (hm : ∀ i, m i < radix)
    (hC : word radix c = NativeSourceMask.gap ports x)
    (hq : NativeBinaryScale.sourceQ ports x = radix ^ n)
    (hM : word radix m = CurrentMasks2011.highPort * x 0 - 1) :
    ∃ k digits : ZMod n → ℕ, (∀ i, k i ≤ 57) ∧ (∀ i, digits i < radix) ∧
      (∀ i, k i = (convolution folded c i +
        NativeWindowCarry.temporalDigits 47 x c i + k (i - 1)) / radix) ∧
      (∀ i, convolution folded c i + NativeWindowCarry.temporalDigits 47 x c i +
        k (i - 1) = digits i + radix * k i) ∧ word radix digits = x 1 ∧
      (∀ i, digits i &&& m i = 0) := by
  have hK : word radix (folded (n := n)) ≡ (ports 1).toNat [MOD radix ^ n - 1] := by
    change word radix (folded (n := n)) ≡ K [MOD radix ^ n - 1]
    exact folded_word (n := n)
  have budget : mass (folded (n := n)) + 2 ^ (47 - 1) + 57 < (57 + 1) * 2 ^ 47 := by
    rw [folded_mass (n := n)]
    decide
  exact NativeWindowCarry.source_convolution_carries (v := 47) (D := 57)
    (by decide) ports interface x hx hs folded c m hc hm hC hq hK hM budget

end DiophantineConsistency.CurrentWindowCarry2011
