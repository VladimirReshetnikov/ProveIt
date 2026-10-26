import DiophantineConsistency.NativeCyclicRotation
import NativeRefactorCore

/-!
Integration candidates. The generic lemmas in NativeRefactorCore are checked.
These wrappers require the pinned ProveIt/Mathlib environment for replay.
-/

namespace DiophantineConsistency.RefactorPrototype

open NativeCyclicRotation

theorem shiftDigits_half_bound_short {n s : Nat} (hs : 0 < s)
    (c : ZMod n → Nat) (hc : ∀ i, c i ≤ 3) (k : ZMod n) :
    shiftDigits (2 * s) s c k ≤ s + 1 := by
  exact halfRadix_bound hs (hc (k - 1))

theorem shiftDigits_half_parity_89_short {n : Nat}
    (c : ZMod n → Nat) (hc : ∀ i, c i ≤ 3) (k : ZMod n) :
    shiftDigits (2 ^ 89) (2 ^ 88) c k % 2 = c (k - 1) / 2 := by
  exact halfRadix_parity (s := 2 ^ 88) (a := c k) (by decide) (by decide) (hc (k - 1))

#print axioms shiftDigits_half_bound_short
#print axioms shiftDigits_half_parity_89_short

end DiophantineConsistency.RefactorPrototype
