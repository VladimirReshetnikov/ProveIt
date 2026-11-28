import GRHArticle.ProgressionFree.IntervalRothExtrema
import GRHArticle.ProgressionFree.PolynomialTwoPrimeBinary

/-!
# Exact interval Roth numbers through 32

At each constant segment, an explicit subset supplies the lower bound
at the left endpoint. A verified mask search supplies the upper bound at
the right endpoint. Monotonicity gives every intermediate value.
-/

namespace GRHArticle.ProgressionFree

set_option maxRecDepth 30000
set_option maxHeartbeats 1500000

private theorem plateau_0 : 0 ≤ rothNumberNat 0 ∧ rothNumberNat 0 ≤ 0 := by
  constructor
  · apply ThreeAPFree.le_rothNumberNat ∅ <;> decide
  · exact rothNumberNat_le_of_byteCheck (by decide +kernel)

private theorem plateau_1 : 1 ≤ rothNumberNat 1 ∧ rothNumberNat 1 ≤ 1 := by
  constructor
  · apply ThreeAPFree.le_rothNumberNat {0} <;> decide
  · exact rothNumberNat_le_of_byteCheck (by decide +kernel)

private theorem plateau_2 : 2 ≤ rothNumberNat 2 ∧ rothNumberNat 3 ≤ 2 := by
  constructor
  · apply ThreeAPFree.le_rothNumberNat {0,1} <;> decide
  · exact rothNumberNat_le_of_byteCheck (by decide +kernel)

private theorem plateau_3 : 3 ≤ rothNumberNat 4 ∧ rothNumberNat 4 ≤ 3 := by
  constructor
  · apply ThreeAPFree.le_rothNumberNat {0,1,3} <;> decide
  · exact rothNumberNat_le_of_byteCheck (by decide +kernel)

private theorem plateau_4 : 4 ≤ rothNumberNat 5 ∧ rothNumberNat 8 ≤ 4 := by
  constructor
  · apply ThreeAPFree.le_rothNumberNat {0,1,3,4} <;> decide
  · exact rothNumberNat_le_of_byteCheck (by decide +kernel)

private theorem plateau_5 : 5 ≤ rothNumberNat 9 ∧ rothNumberNat 10 ≤ 5 := by
  constructor
  · apply ThreeAPFree.le_rothNumberNat {0,1,3,7,8} <;> decide
  · exact rothNumberNat_le_of_byteCheck (by decide +kernel)

private theorem plateau_6 : 6 ≤ rothNumberNat 11 ∧ rothNumberNat 12 ≤ 6 := by
  constructor
  · apply ThreeAPFree.le_rothNumberNat {0,1,3,4,9,10} <;> decide
  · exact rothNumberNat_le_of_byteCheck (by decide +kernel)

private theorem plateau_7 : 7 ≤ rothNumberNat 13 ∧ rothNumberNat 13 ≤ 7 := by
  constructor
  · apply ThreeAPFree.le_rothNumberNat {0,1,3,4,9,10,12} <;> decide
  · exact rothNumberNat_le_of_byteCheck (by decide +kernel)

private theorem plateau_8 : 8 ≤ rothNumberNat 14 ∧ rothNumberNat 19 ≤ 8 := by
  constructor
  · apply ThreeAPFree.le_rothNumberNat {0,1,3,4,9,10,12,13} <;> decide
  · exact rothNumberNat_le_of_byteCheck (by decide +kernel)

private theorem plateau_9 : 9 ≤ rothNumberNat 20 ∧ rothNumberNat 23 ≤ 9 := by
  constructor
  · apply ThreeAPFree.le_rothNumberNat {0,1,5,6,8,13,14,17,19} <;> decide
  · exact rothNumberNat_le_of_byteCheck (by decide +kernel)

private theorem plateau_10 : 10 ≤ rothNumberNat 24 ∧ rothNumberNat 25 ≤ 10 := by
  constructor
  · apply ThreeAPFree.le_rothNumberNat {0,1,4,6,10,15,17,18,22,23} <;> decide
  · exact rothNumberNat_le_of_byteCheck (by decide +kernel)

private theorem plateau_11 : 11 ≤ rothNumberNat 26 ∧ rothNumberNat 29 ≤ 11 := by
  constructor
  · apply ThreeAPFree.le_rothNumberNat {0,1,4,6,10,15,17,18,22,23,25} <;> decide
  · exact rothNumberNat_le_of_byteCheck (by decide +kernel)

private theorem plateau_12 : 12 ≤ rothNumberNat 30 ∧ rothNumberNat 31 ≤ 12 := by
  constructor
  · apply ThreeAPFree.le_rothNumberNat {0,2,3,7,8,10,19,21,22,26,27,29} <;> decide
  · exact rothNumberNat_le_of_byteCheck (by decide +kernel)

private theorem plateau_13 : 13 ≤ rothNumberNat 32 ∧ rothNumberNat 32 ≤ 13 := by
  constructor
  · apply ThreeAPFree.le_rothNumberNat {0,1,3,7,8,10,18,21,22,25,27,30,31} <;> decide
  · exact rothNumberNat_le_of_byteCheck (by decide +kernel)

private theorem roth_plateau {n lo hi v : ℕ} (h : v ≤ rothNumberNat lo ∧ rothNumberNat hi ≤ v)
    (hl : lo ≤ n) (hu : n ≤ hi) : rothNumberNat n = v :=
  le_antisymm ((rothNumberNat.monotone hu).trans h.2) (h.1.trans (rothNumberNat.monotone hl))

/-- Every entry of the table used for the binary polynomial-density bound
equals Mathlib's actual Roth number of the indicated interval. -/
theorem rothNumberNat_eq_binaryRothNumberTable (n : ℕ) (hn : n ≤ 32) :
    rothNumberNat n = binaryRothNumberTable n := by
  interval_cases n <;> first
    | exact roth_plateau plateau_0 (by decide) (by decide)
    | exact roth_plateau plateau_1 (by decide) (by decide)
    | exact roth_plateau plateau_2 (by decide) (by decide)
    | exact roth_plateau plateau_3 (by decide) (by decide)
    | exact roth_plateau plateau_4 (by decide) (by decide)
    | exact roth_plateau plateau_5 (by decide) (by decide)
    | exact roth_plateau plateau_6 (by decide) (by decide)
    | exact roth_plateau plateau_7 (by decide) (by decide)
    | exact roth_plateau plateau_8 (by decide) (by decide)
    | exact roth_plateau plateau_9 (by decide) (by decide)
    | exact roth_plateau plateau_10 (by decide) (by decide)
    | exact roth_plateau plateau_11 (by decide) (by decide)
    | exact roth_plateau plateau_12 (by decide) (by decide)
    | exact roth_plateau plateau_13 (by decide) (by decide)

end GRHArticle.ProgressionFree
