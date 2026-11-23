import Lean

/-! The integer cancellation used after clearing rational edge denominators.
This file is a standalone Lean 4 source for the semantic finite sum lemma. -/

namespace TopologyIPRA.Winding

def prefixSum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => prefixSum f n + f n

/-- The difference between two rows is the difference at their ends. -/
theorem strip (b t v : Nat → Int) (n : Nat)
    (cell : ∀ i, i < n → b i + v (i + 1) = v i + t i) :
    prefixSum b n + v n = v 0 + prefixSum t n := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
    have a := ih (fun i hi => cell i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    have z := cell n (Nat.lt_succ_self n)
    simp only [prefixSum]
    omega

/-- Periodic vertical seams force equal signed sums on the first and last row. -/
theorem periodicRows (h v : Nat → Nat → Int) (width height : Nat)
    (cell : ∀ j, j < height → ∀ i, i < width →
      h j i + v j (i + 1) = v j i + h (j + 1) i)
    (seam : ∀ j, j < height → v j width = v j 0) :
    prefixSum (h 0) width = prefixSum (h height) width := by
  induction height with
  | zero => rfl
  | succ n ih =>
    have previous := ih
      (fun j hj => cell j (Nat.lt_trans hj (Nat.lt_succ_self n)))
      (fun j hj => seam j (Nat.lt_trans hj (Nat.lt_succ_self n)))
    have nextRow := strip (h n) (h (n + 1)) (v n) width (cell n (Nat.lt_succ_self n))
    have sameEnds := seam n (Nat.lt_succ_self n)
    omega

end TopologyIPRA.Winding
