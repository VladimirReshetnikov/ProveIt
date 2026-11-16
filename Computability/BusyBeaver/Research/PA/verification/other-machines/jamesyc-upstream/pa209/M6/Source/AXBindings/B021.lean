module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row3403_u0 : resolveAt exactSites 3403 = some (UnpairPartial.expected 3403 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_u1 : resolveAt exactSites 3404 = some (UnpairPartial.expected 3403 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_u2 : resolveAt exactSites 3405 = some (UnpairPartial.expected 3403 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_u3 : resolveAt exactSites 3406 = some (UnpairPartial.expected 3403 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_u4 : resolveAt exactSites 3407 = some (UnpairPartial.expected 3403 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_u5 : resolveAt exactSites 3408 = some (UnpairPartial.expected 3403 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_u6 : resolveAt exactSites 3409 = some (UnpairPartial.expected 3403 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_u7 : resolveAt exactSites 3410 = some (UnpairPartial.expected 3403 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_u8 : resolveAt exactSites 3411 = some (UnpairPartial.expected 3403 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_u9 : resolveAt exactSites 3412 = some (UnpairPartial.expected 3403 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_u10 : resolveAt exactSites 3413 = some (UnpairPartial.expected 3403 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3403_u : UnpairPartial.Bound exactSites 3403 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3403_u0
  · exact row3403_u1
  · exact row3403_u2
  · exact row3403_u3
  · exact row3403_u4
  · exact row3403_u5
  · exact row3403_u6
  · exact row3403_u7
  · exact row3403_u8
  · exact row3403_u9
  · exact row3403_u10
private theorem row3403_q0 : resolveAt exactSites 3414 = some (AXPair.relocate 3383 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_q1 : resolveAt exactSites 3415 = some (AXPair.relocate 3383 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_q2 : resolveAt exactSites 3416 = some (AXPair.relocate 3383 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_q3 : resolveAt exactSites 3417 = some (AXPair.relocate 3383 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_q4 : resolveAt exactSites 3418 = some (AXPair.relocate 3383 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_q5 : resolveAt exactSites 3419 = some (AXPair.relocate 3383 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_q6 : resolveAt exactSites 3420 = some (AXPair.relocate 3383 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_q7 : resolveAt exactSites 3421 = some (AXPair.relocate 3383 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_q8 : resolveAt exactSites 3422 = some (AXPair.relocate 3383 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_q9 : resolveAt exactSites 3423 = some (AXPair.relocate 3383 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3403_q : AXPair.Bound exactSites 3383 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3403_q0
  · exact row3403_q1
  · exact row3403_q2
  · exact row3403_q3
  · exact row3403_q4
  · exact row3403_q5
  · exact row3403_q6
  · exact row3403_q7
  · exact row3403_q8
  · exact row3403_q9
private theorem row3403_m0 : resolveAt exactSites 3424 = some (AXTimes4.expected 3424 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_m1 : resolveAt exactSites 3425 = some (AXTimes4.expected 3424 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_m2 : resolveAt exactSites 3426 = some (AXTimes4.expected 3424 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_m3 : resolveAt exactSites 3427 = some (AXTimes4.expected 3424 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_m4 : resolveAt exactSites 3428 = some (AXTimes4.expected 3424 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3403_m5 : resolveAt exactSites 3429 = some (AXTimes4.expected 3424 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3403_m : AXTimes4.Bound exactSites 3424 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3403_m0
  · exact row3403_m1
  · exact row3403_m2
  · exact row3403_m3
  · exact row3403_m4
  · exact row3403_m5
theorem block3403 : AXMacro.Realizes exactSites .cons 3403 3430 :=
  AXMacro.cons_realizes bound3403_u bound3403_q bound3403_m
private theorem row3430_u0 : resolveAt exactSites 3430 = some (UnpairPartial.expected 3430 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_u1 : resolveAt exactSites 3431 = some (UnpairPartial.expected 3430 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_u2 : resolveAt exactSites 3432 = some (UnpairPartial.expected 3430 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_u3 : resolveAt exactSites 3433 = some (UnpairPartial.expected 3430 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_u4 : resolveAt exactSites 3434 = some (UnpairPartial.expected 3430 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_u5 : resolveAt exactSites 3435 = some (UnpairPartial.expected 3430 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_u6 : resolveAt exactSites 3436 = some (UnpairPartial.expected 3430 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_u7 : resolveAt exactSites 3437 = some (UnpairPartial.expected 3430 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_u8 : resolveAt exactSites 3438 = some (UnpairPartial.expected 3430 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_u9 : resolveAt exactSites 3439 = some (UnpairPartial.expected 3430 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_u10 : resolveAt exactSites 3440 = some (UnpairPartial.expected 3430 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3430_u : UnpairPartial.Bound exactSites 3430 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3430_u0
  · exact row3430_u1
  · exact row3430_u2
  · exact row3430_u3
  · exact row3430_u4
  · exact row3430_u5
  · exact row3430_u6
  · exact row3430_u7
  · exact row3430_u8
  · exact row3430_u9
  · exact row3430_u10
private theorem row3430_q0 : resolveAt exactSites 3441 = some (AXPair.relocate 3410 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_q1 : resolveAt exactSites 3442 = some (AXPair.relocate 3410 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_q2 : resolveAt exactSites 3443 = some (AXPair.relocate 3410 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_q3 : resolveAt exactSites 3444 = some (AXPair.relocate 3410 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_q4 : resolveAt exactSites 3445 = some (AXPair.relocate 3410 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_q5 : resolveAt exactSites 3446 = some (AXPair.relocate 3410 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_q6 : resolveAt exactSites 3447 = some (AXPair.relocate 3410 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_q7 : resolveAt exactSites 3448 = some (AXPair.relocate 3410 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_q8 : resolveAt exactSites 3449 = some (AXPair.relocate 3410 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_q9 : resolveAt exactSites 3450 = some (AXPair.relocate 3410 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3430_q : AXPair.Bound exactSites 3410 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3430_q0
  · exact row3430_q1
  · exact row3430_q2
  · exact row3430_q3
  · exact row3430_q4
  · exact row3430_q5
  · exact row3430_q6
  · exact row3430_q7
  · exact row3430_q8
  · exact row3430_q9
private theorem row3430_m0 : resolveAt exactSites 3451 = some (AXTimes4.expected 3451 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_m1 : resolveAt exactSites 3452 = some (AXTimes4.expected 3451 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_m2 : resolveAt exactSites 3453 = some (AXTimes4.expected 3451 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_m3 : resolveAt exactSites 3454 = some (AXTimes4.expected 3451 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_m4 : resolveAt exactSites 3455 = some (AXTimes4.expected 3451 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3430_m5 : resolveAt exactSites 3456 = some (AXTimes4.expected 3451 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3430_m : AXTimes4.Bound exactSites 3451 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3430_m0
  · exact row3430_m1
  · exact row3430_m2
  · exact row3430_m3
  · exact row3430_m4
  · exact row3430_m5
theorem block3430 : AXMacro.Realizes exactSites .cons 3430 3457 :=
  AXMacro.cons_realizes bound3430_u bound3430_q bound3430_m
private theorem row3457_i0 : resolveAt exactSites 3457 = some (Instruction.inc 1 (some 3458)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block3457 : AXMacro.Realizes exactSites .incT 3457 3458 :=
  AXMacro.inc_realizes row3457_i0
private theorem row3458_i0 : resolveAt exactSites 3458 = some (Instruction.inc 1 (some 3459)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block3458 : AXMacro.Realizes exactSites .incT 3458 3459 :=
  AXMacro.inc_realizes row3458_i0
private theorem row3459_p0 : resolveAt exactSites 3459 = some (AXPushParam.relocate 3434 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p1 : resolveAt exactSites 3460 = some (AXPushParam.relocate 3434 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p2 : resolveAt exactSites 3461 = some (AXPushParam.relocate 3434 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p3 : resolveAt exactSites 3462 = some (AXPushParam.relocate 3434 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p4 : resolveAt exactSites 3463 = some (AXPushParam.relocate 3434 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p5 : resolveAt exactSites 3464 = some (AXPushParam.relocate 3434 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p6 : resolveAt exactSites 3465 = some (AXPushParam.relocate 3434 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p7 : resolveAt exactSites 3466 = some (AXPushParam.relocate 3434 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p8 : resolveAt exactSites 3467 = some (AXPushParam.relocate 3434 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p9 : resolveAt exactSites 3468 = some (AXPushParam.relocate 3434 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p10 : resolveAt exactSites 3469 = some (AXPushParam.relocate 3434 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p11 : resolveAt exactSites 3470 = some (AXPushParam.relocate 3434 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p12 : resolveAt exactSites 3471 = some (AXPushParam.relocate 3434 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p13 : resolveAt exactSites 3472 = some (AXPushParam.relocate 3434 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p14 : resolveAt exactSites 3473 = some (AXPushParam.relocate 3434 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p15 : resolveAt exactSites 3474 = some (AXPushParam.relocate 3434 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p16 : resolveAt exactSites 3475 = some (AXPushParam.relocate 3434 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p17 : resolveAt exactSites 3476 = some (AXPushParam.relocate 3434 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3459_p18 : resolveAt exactSites 3477 = some (AXPushParam.relocate 3434 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3459_p : AXPushParam.Bound exactSites 3434 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3459_p0
  · exact row3459_p1
  · exact row3459_p2
  · exact row3459_p3
  · exact row3459_p4
  · exact row3459_p5
  · exact row3459_p6
  · exact row3459_p7
  · exact row3459_p8
  · exact row3459_p9
  · exact row3459_p10
  · exact row3459_p11
  · exact row3459_p12
  · exact row3459_p13
  · exact row3459_p14
  · exact row3459_p15
  · exact row3459_p16
  · exact row3459_p17
  · exact row3459_p18
theorem block3459 : AXMacro.Realizes exactSites .push 3459 3478 :=
  AXMacro.push_realizes bound3459_p
private theorem row3478_c0 : resolveAt exactSites 3478 = some (CopyToT.expected 3 3478 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3478_c1 : resolveAt exactSites 3479 = some (CopyToT.expected 3 3478 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3478_c2 : resolveAt exactSites 3480 = some (CopyToT.expected 3 3478 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3478_c3 : resolveAt exactSites 3481 = some (CopyToT.expected 3 3478 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3478_c4 : resolveAt exactSites 3482 = some (CopyToT.expected 3 3478 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3478_c5 : resolveAt exactSites 3483 = some (CopyToT.expected 3 3478 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3478_c6 : resolveAt exactSites 3484 = some (CopyToT.expected 3 3478 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3478_c : CopyToT.Bound exactSites 3 3478 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3478_c0
  · exact row3478_c1
  · exact row3478_c2
  · exact row3478_c3
  · exact row3478_c4
  · exact row3478_c5
  · exact row3478_c6
theorem block3478 : AXMacro.Realizes exactSites .copyA 3478 3485 :=
  AXMacro.copyA_realizes bound3478_c
private theorem row3485_p0 : resolveAt exactSites 3485 = some (AXPushParam.relocate 3460 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p1 : resolveAt exactSites 3486 = some (AXPushParam.relocate 3460 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p2 : resolveAt exactSites 3487 = some (AXPushParam.relocate 3460 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p3 : resolveAt exactSites 3488 = some (AXPushParam.relocate 3460 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p4 : resolveAt exactSites 3489 = some (AXPushParam.relocate 3460 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p5 : resolveAt exactSites 3490 = some (AXPushParam.relocate 3460 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p6 : resolveAt exactSites 3491 = some (AXPushParam.relocate 3460 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p7 : resolveAt exactSites 3492 = some (AXPushParam.relocate 3460 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p8 : resolveAt exactSites 3493 = some (AXPushParam.relocate 3460 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p9 : resolveAt exactSites 3494 = some (AXPushParam.relocate 3460 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p10 : resolveAt exactSites 3495 = some (AXPushParam.relocate 3460 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p11 : resolveAt exactSites 3496 = some (AXPushParam.relocate 3460 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p12 : resolveAt exactSites 3497 = some (AXPushParam.relocate 3460 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p13 : resolveAt exactSites 3498 = some (AXPushParam.relocate 3460 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p14 : resolveAt exactSites 3499 = some (AXPushParam.relocate 3460 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p15 : resolveAt exactSites 3500 = some (AXPushParam.relocate 3460 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p16 : resolveAt exactSites 3501 = some (AXPushParam.relocate 3460 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p17 : resolveAt exactSites 3502 = some (AXPushParam.relocate 3460 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3485_p18 : resolveAt exactSites 3503 = some (AXPushParam.relocate 3460 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3485_p : AXPushParam.Bound exactSites 3460 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3485_p0
  · exact row3485_p1
  · exact row3485_p2
  · exact row3485_p3
  · exact row3485_p4
  · exact row3485_p5
  · exact row3485_p6
  · exact row3485_p7
  · exact row3485_p8
  · exact row3485_p9
  · exact row3485_p10
  · exact row3485_p11
  · exact row3485_p12
  · exact row3485_p13
  · exact row3485_p14
  · exact row3485_p15
  · exact row3485_p16
  · exact row3485_p17
  · exact row3485_p18
theorem block3485 : AXMacro.Realizes exactSites .push 3485 3504 :=
  AXMacro.push_realizes bound3485_p
private theorem row3504_c0 : resolveAt exactSites 3504 = some (CopyToT.expected 3 3504 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3504_c1 : resolveAt exactSites 3505 = some (CopyToT.expected 3 3504 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3504_c2 : resolveAt exactSites 3506 = some (CopyToT.expected 3 3504 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3504_c3 : resolveAt exactSites 3507 = some (CopyToT.expected 3 3504 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3504_c4 : resolveAt exactSites 3508 = some (CopyToT.expected 3 3504 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3504_c5 : resolveAt exactSites 3509 = some (CopyToT.expected 3 3504 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3504_c6 : resolveAt exactSites 3510 = some (CopyToT.expected 3 3504 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3504_c : CopyToT.Bound exactSites 3 3504 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3504_c0
  · exact row3504_c1
  · exact row3504_c2
  · exact row3504_c3
  · exact row3504_c4
  · exact row3504_c5
  · exact row3504_c6
theorem block3504 : AXMacro.Realizes exactSites .copyA 3504 3511 :=
  AXMacro.copyA_realizes bound3504_c
private theorem row3511_p0 : resolveAt exactSites 3511 = some (AXPushParam.relocate 3486 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p1 : resolveAt exactSites 3512 = some (AXPushParam.relocate 3486 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p2 : resolveAt exactSites 3513 = some (AXPushParam.relocate 3486 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p3 : resolveAt exactSites 3514 = some (AXPushParam.relocate 3486 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p4 : resolveAt exactSites 3515 = some (AXPushParam.relocate 3486 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p5 : resolveAt exactSites 3516 = some (AXPushParam.relocate 3486 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p6 : resolveAt exactSites 3517 = some (AXPushParam.relocate 3486 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p7 : resolveAt exactSites 3518 = some (AXPushParam.relocate 3486 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p8 : resolveAt exactSites 3519 = some (AXPushParam.relocate 3486 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p9 : resolveAt exactSites 3520 = some (AXPushParam.relocate 3486 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p10 : resolveAt exactSites 3521 = some (AXPushParam.relocate 3486 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p11 : resolveAt exactSites 3522 = some (AXPushParam.relocate 3486 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p12 : resolveAt exactSites 3523 = some (AXPushParam.relocate 3486 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p13 : resolveAt exactSites 3524 = some (AXPushParam.relocate 3486 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p14 : resolveAt exactSites 3525 = some (AXPushParam.relocate 3486 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p15 : resolveAt exactSites 3526 = some (AXPushParam.relocate 3486 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p16 : resolveAt exactSites 3527 = some (AXPushParam.relocate 3486 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p17 : resolveAt exactSites 3528 = some (AXPushParam.relocate 3486 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3511_p18 : resolveAt exactSites 3529 = some (AXPushParam.relocate 3486 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3511_p : AXPushParam.Bound exactSites 3486 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3511_p0
  · exact row3511_p1
  · exact row3511_p2
  · exact row3511_p3
  · exact row3511_p4
  · exact row3511_p5
  · exact row3511_p6
  · exact row3511_p7
  · exact row3511_p8
  · exact row3511_p9
  · exact row3511_p10
  · exact row3511_p11
  · exact row3511_p12
  · exact row3511_p13
  · exact row3511_p14
  · exact row3511_p15
  · exact row3511_p16
  · exact row3511_p17
  · exact row3511_p18
theorem block3511 : AXMacro.Realizes exactSites .push 3511 3530 :=
  AXMacro.push_realizes bound3511_p
private theorem row3530_c0 : resolveAt exactSites 3530 = some (CopyToT.expected 5 3530 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3530_c1 : resolveAt exactSites 3531 = some (CopyToT.expected 5 3530 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3530_c2 : resolveAt exactSites 3532 = some (CopyToT.expected 5 3530 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3530_c3 : resolveAt exactSites 3533 = some (CopyToT.expected 5 3530 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3530_c4 : resolveAt exactSites 3534 = some (CopyToT.expected 5 3530 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3530_c5 : resolveAt exactSites 3535 = some (CopyToT.expected 5 3530 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3530_c6 : resolveAt exactSites 3536 = some (CopyToT.expected 5 3530 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3530_c : CopyToT.Bound exactSites 5 3530 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3530_c0
  · exact row3530_c1
  · exact row3530_c2
  · exact row3530_c3
  · exact row3530_c4
  · exact row3530_c5
  · exact row3530_c6
theorem block3530 : AXMacro.Realizes exactSites .copyH 3530 3537 :=
  AXMacro.copyH_realizes bound3530_c
private theorem row3537_u0 : resolveAt exactSites 3537 = some (UnpairPartial.expected 3537 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_u1 : resolveAt exactSites 3538 = some (UnpairPartial.expected 3537 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_u2 : resolveAt exactSites 3539 = some (UnpairPartial.expected 3537 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_u3 : resolveAt exactSites 3540 = some (UnpairPartial.expected 3537 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_u4 : resolveAt exactSites 3541 = some (UnpairPartial.expected 3537 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_u5 : resolveAt exactSites 3542 = some (UnpairPartial.expected 3537 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_u6 : resolveAt exactSites 3543 = some (UnpairPartial.expected 3537 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_u7 : resolveAt exactSites 3544 = some (UnpairPartial.expected 3537 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_u8 : resolveAt exactSites 3545 = some (UnpairPartial.expected 3537 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_u9 : resolveAt exactSites 3546 = some (UnpairPartial.expected 3537 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_u10 : resolveAt exactSites 3547 = some (UnpairPartial.expected 3537 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3537_u : UnpairPartial.Bound exactSites 3537 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3537_u0
  · exact row3537_u1
  · exact row3537_u2
  · exact row3537_u3
  · exact row3537_u4
  · exact row3537_u5
  · exact row3537_u6
  · exact row3537_u7
  · exact row3537_u8
  · exact row3537_u9
  · exact row3537_u10
private theorem row3537_q0 : resolveAt exactSites 3548 = some (AXPair.relocate 3517 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_q1 : resolveAt exactSites 3549 = some (AXPair.relocate 3517 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_q2 : resolveAt exactSites 3550 = some (AXPair.relocate 3517 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_q3 : resolveAt exactSites 3551 = some (AXPair.relocate 3517 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_q4 : resolveAt exactSites 3552 = some (AXPair.relocate 3517 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_q5 : resolveAt exactSites 3553 = some (AXPair.relocate 3517 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_q6 : resolveAt exactSites 3554 = some (AXPair.relocate 3517 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_q7 : resolveAt exactSites 3555 = some (AXPair.relocate 3517 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_q8 : resolveAt exactSites 3556 = some (AXPair.relocate 3517 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_q9 : resolveAt exactSites 3557 = some (AXPair.relocate 3517 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3537_q : AXPair.Bound exactSites 3517 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3537_q0
  · exact row3537_q1
  · exact row3537_q2
  · exact row3537_q3
  · exact row3537_q4
  · exact row3537_q5
  · exact row3537_q6
  · exact row3537_q7
  · exact row3537_q8
  · exact row3537_q9
private theorem row3537_m0 : resolveAt exactSites 3558 = some (AXTimes4.expected 3558 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_m1 : resolveAt exactSites 3559 = some (AXTimes4.expected 3558 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_m2 : resolveAt exactSites 3560 = some (AXTimes4.expected 3558 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_m3 : resolveAt exactSites 3561 = some (AXTimes4.expected 3558 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_m4 : resolveAt exactSites 3562 = some (AXTimes4.expected 3558 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3537_m5 : resolveAt exactSites 3563 = some (AXTimes4.expected 3558 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3537_m : AXTimes4.Bound exactSites 3558 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3537_m0
  · exact row3537_m1
  · exact row3537_m2
  · exact row3537_m3
  · exact row3537_m4
  · exact row3537_m5
theorem block3537 : AXMacro.Realizes exactSites .cons 3537 3564 :=
  AXMacro.cons_realizes bound3537_u bound3537_q bound3537_m
private theorem row3564_i0 : resolveAt exactSites 3564 = some (Instruction.inc 1 (some 3565)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block3564 : AXMacro.Realizes exactSites .incT 3564 3565 :=
  AXMacro.inc_realizes row3564_i0
def code021 : List AXMacro.Op := [.cons,.cons,.incT,.incT,.push,.copyA,.push,.copyA,.push,.copyH,.cons,.incT]
theorem plan021 : AXMacro.Plan exactSites 3403 3565 code021 :=
  AXMacro.Plan.cons block3403 ( AXMacro.Plan.cons block3430 ( AXMacro.Plan.cons block3457 ( AXMacro.Plan.cons block3458 ( AXMacro.Plan.cons block3459 ( AXMacro.Plan.cons block3478 ( AXMacro.Plan.cons block3485 ( AXMacro.Plan.cons block3504 ( AXMacro.Plan.cons block3511 ( AXMacro.Plan.cons block3530 ( AXMacro.Plan.cons block3537 ( AXMacro.Plan.cons block3564 ( AXMacro.Plan.nil 3565))))))))))))
#print axioms plan021
end M6.Source.AXAll

