import RamseyPaperCommon.ThreeFreeCounting

/-!
# Exact finite counting certificates

The native decision procedure evaluates the reviewed prefix-extension
recurrence in `ThreeFreeCounting`.  This single computation certifies every
finite value quoted by the three papers through `n = 20`.
-/

set_option autoImplicit false

namespace LeanProofs.RamseyPaperCommon

set_option maxHeartbeats 0 in
/-- The shared three-progression-free permutation sequence through `n = 20`. -/
theorem reflectedM_values_through_twenty :
    reflectedM 1 = 1 /\
    reflectedM 2 = 2 /\
    reflectedM 3 = 4 /\
    reflectedM 4 = 10 /\
    reflectedM 5 = 20 /\
    reflectedM 6 = 48 /\
    reflectedM 7 = 104 /\
    reflectedM 8 = 282 /\
    reflectedM 9 = 496 /\
    reflectedM 10 = 1066 /\
    reflectedM 11 = 2460 /\
    reflectedM 12 = 6128 /\
    reflectedM 13 = 12840 /\
    reflectedM 14 = 29380 /\
    reflectedM 15 = 74904 /\
    reflectedM 16 = 212728 /\
    reflectedM 17 = 368016 /\
    reflectedM 18 = 659296 /\
    reflectedM 19 = 1371056 /\
    reflectedM 20 = 2937136 := by
  native_decide

end LeanProofs.RamseyPaperCommon
