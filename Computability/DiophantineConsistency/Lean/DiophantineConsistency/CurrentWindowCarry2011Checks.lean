import DiophantineConsistency.CurrentWindowCarry2011

namespace DiophantineConsistency.CurrentWindowCarry2011Checks

open CurrentKernel2011 CurrentWindowCarry2011 NativeCyclicConvolution

example : ports 1 = (K : ℤ) := rfl

example : ports 0 = (CurrentMasks2011.beta : ℤ) ∧
    ports 2 = (CurrentMasks2011.lowPort : ℤ) ∧
    ports 3 = ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : ℤ) :=
  ⟨rfl, rfl, rfl⟩

example : (0 : ℤ) < ports 1 := by
  change (0 : ℤ) < (K : ℤ)
  exact_mod_cast K_pos

example {n : ℕ} [NeZero n] (x : Fin 31 → ℕ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, SplitCertificate59.sourceRows ports (fun k => (x k : ℤ)) j = 0)
    (c m : ZMod n → ℕ) (hc : ∀ i, c i ≤ 1) (hm : ∀ i, m i < radix)
    (hC : word radix c = NativeSourceMask.gap ports x)
    (hq : NativeBinaryScale.sourceQ ports x = radix ^ n)
    (hM : word radix m = CurrentMasks2011.highPort * x 0 - 1) :
    ∃ digits : ZMod n → ℕ, word radix digits = x 1 ∧
      (∀ i, digits i < radix) ∧ (∀ i, digits i &&& m i = 0) := by
  obtain ⟨_, digits, _, hd, _, _, hw, hmasks⟩ := source_carries x hx hs c m hc hm hC hq hM
  exact ⟨digits, hw, hd, hmasks⟩

#print axioms interface
#print axioms source_carries

end DiophantineConsistency.CurrentWindowCarry2011Checks
