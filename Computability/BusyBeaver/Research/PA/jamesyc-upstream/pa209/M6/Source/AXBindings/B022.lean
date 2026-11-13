module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row3565_u0 : resolveAt exactSites 3565 = some (UnpairPartial.expected 3565 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_u1 : resolveAt exactSites 3566 = some (UnpairPartial.expected 3565 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_u2 : resolveAt exactSites 3567 = some (UnpairPartial.expected 3565 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_u3 : resolveAt exactSites 3568 = some (UnpairPartial.expected 3565 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_u4 : resolveAt exactSites 3569 = some (UnpairPartial.expected 3565 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_u5 : resolveAt exactSites 3570 = some (UnpairPartial.expected 3565 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_u6 : resolveAt exactSites 3571 = some (UnpairPartial.expected 3565 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_u7 : resolveAt exactSites 3572 = some (UnpairPartial.expected 3565 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_u8 : resolveAt exactSites 3573 = some (UnpairPartial.expected 3565 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_u9 : resolveAt exactSites 3574 = some (UnpairPartial.expected 3565 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_u10 : resolveAt exactSites 3575 = some (UnpairPartial.expected 3565 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3565_u : UnpairPartial.Bound exactSites 3565 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3565_u0
  · exact row3565_u1
  · exact row3565_u2
  · exact row3565_u3
  · exact row3565_u4
  · exact row3565_u5
  · exact row3565_u6
  · exact row3565_u7
  · exact row3565_u8
  · exact row3565_u9
  · exact row3565_u10
private theorem row3565_q0 : resolveAt exactSites 3576 = some (AXPair.relocate 3545 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_q1 : resolveAt exactSites 3577 = some (AXPair.relocate 3545 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_q2 : resolveAt exactSites 3578 = some (AXPair.relocate 3545 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_q3 : resolveAt exactSites 3579 = some (AXPair.relocate 3545 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_q4 : resolveAt exactSites 3580 = some (AXPair.relocate 3545 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_q5 : resolveAt exactSites 3581 = some (AXPair.relocate 3545 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_q6 : resolveAt exactSites 3582 = some (AXPair.relocate 3545 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_q7 : resolveAt exactSites 3583 = some (AXPair.relocate 3545 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_q8 : resolveAt exactSites 3584 = some (AXPair.relocate 3545 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_q9 : resolveAt exactSites 3585 = some (AXPair.relocate 3545 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3565_q : AXPair.Bound exactSites 3545 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3565_q0
  · exact row3565_q1
  · exact row3565_q2
  · exact row3565_q3
  · exact row3565_q4
  · exact row3565_q5
  · exact row3565_q6
  · exact row3565_q7
  · exact row3565_q8
  · exact row3565_q9
private theorem row3565_m0 : resolveAt exactSites 3586 = some (AXTimes4.expected 3586 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_m1 : resolveAt exactSites 3587 = some (AXTimes4.expected 3586 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_m2 : resolveAt exactSites 3588 = some (AXTimes4.expected 3586 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_m3 : resolveAt exactSites 3589 = some (AXTimes4.expected 3586 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_m4 : resolveAt exactSites 3590 = some (AXTimes4.expected 3586 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3565_m5 : resolveAt exactSites 3591 = some (AXTimes4.expected 3586 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3565_m : AXTimes4.Bound exactSites 3586 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3565_m0
  · exact row3565_m1
  · exact row3565_m2
  · exact row3565_m3
  · exact row3565_m4
  · exact row3565_m5
theorem block3565 : AXMacro.Realizes exactSites .cons 3565 3592 :=
  AXMacro.cons_realizes bound3565_u bound3565_q bound3565_m
private theorem row3592_p0 : resolveAt exactSites 3592 = some (AXPushParam.relocate 3567 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p1 : resolveAt exactSites 3593 = some (AXPushParam.relocate 3567 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p2 : resolveAt exactSites 3594 = some (AXPushParam.relocate 3567 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p3 : resolveAt exactSites 3595 = some (AXPushParam.relocate 3567 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p4 : resolveAt exactSites 3596 = some (AXPushParam.relocate 3567 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p5 : resolveAt exactSites 3597 = some (AXPushParam.relocate 3567 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p6 : resolveAt exactSites 3598 = some (AXPushParam.relocate 3567 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p7 : resolveAt exactSites 3599 = some (AXPushParam.relocate 3567 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p8 : resolveAt exactSites 3600 = some (AXPushParam.relocate 3567 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p9 : resolveAt exactSites 3601 = some (AXPushParam.relocate 3567 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p10 : resolveAt exactSites 3602 = some (AXPushParam.relocate 3567 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p11 : resolveAt exactSites 3603 = some (AXPushParam.relocate 3567 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p12 : resolveAt exactSites 3604 = some (AXPushParam.relocate 3567 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p13 : resolveAt exactSites 3605 = some (AXPushParam.relocate 3567 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p14 : resolveAt exactSites 3606 = some (AXPushParam.relocate 3567 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p15 : resolveAt exactSites 3607 = some (AXPushParam.relocate 3567 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p16 : resolveAt exactSites 3608 = some (AXPushParam.relocate 3567 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p17 : resolveAt exactSites 3609 = some (AXPushParam.relocate 3567 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3592_p18 : resolveAt exactSites 3610 = some (AXPushParam.relocate 3567 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3592_p : AXPushParam.Bound exactSites 3567 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3592_p0
  · exact row3592_p1
  · exact row3592_p2
  · exact row3592_p3
  · exact row3592_p4
  · exact row3592_p5
  · exact row3592_p6
  · exact row3592_p7
  · exact row3592_p8
  · exact row3592_p9
  · exact row3592_p10
  · exact row3592_p11
  · exact row3592_p12
  · exact row3592_p13
  · exact row3592_p14
  · exact row3592_p15
  · exact row3592_p16
  · exact row3592_p17
  · exact row3592_p18
theorem block3592 : AXMacro.Realizes exactSites .push 3592 3611 :=
  AXMacro.push_realizes bound3592_p
private theorem row3611_i0 : resolveAt exactSites 3611 = some (Instruction.inc 1 (some 3612)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block3611 : AXMacro.Realizes exactSites .incT 3611 3612 :=
  AXMacro.inc_realizes row3611_i0
private theorem row3612_u0 : resolveAt exactSites 3612 = some (UnpairPartial.expected 3612 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_u1 : resolveAt exactSites 3613 = some (UnpairPartial.expected 3612 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_u2 : resolveAt exactSites 3614 = some (UnpairPartial.expected 3612 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_u3 : resolveAt exactSites 3615 = some (UnpairPartial.expected 3612 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_u4 : resolveAt exactSites 3616 = some (UnpairPartial.expected 3612 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_u5 : resolveAt exactSites 3617 = some (UnpairPartial.expected 3612 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_u6 : resolveAt exactSites 3618 = some (UnpairPartial.expected 3612 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_u7 : resolveAt exactSites 3619 = some (UnpairPartial.expected 3612 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_u8 : resolveAt exactSites 3620 = some (UnpairPartial.expected 3612 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_u9 : resolveAt exactSites 3621 = some (UnpairPartial.expected 3612 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_u10 : resolveAt exactSites 3622 = some (UnpairPartial.expected 3612 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3612_u : UnpairPartial.Bound exactSites 3612 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3612_u0
  · exact row3612_u1
  · exact row3612_u2
  · exact row3612_u3
  · exact row3612_u4
  · exact row3612_u5
  · exact row3612_u6
  · exact row3612_u7
  · exact row3612_u8
  · exact row3612_u9
  · exact row3612_u10
private theorem row3612_q0 : resolveAt exactSites 3623 = some (AXPair.relocate 3592 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_q1 : resolveAt exactSites 3624 = some (AXPair.relocate 3592 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_q2 : resolveAt exactSites 3625 = some (AXPair.relocate 3592 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_q3 : resolveAt exactSites 3626 = some (AXPair.relocate 3592 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_q4 : resolveAt exactSites 3627 = some (AXPair.relocate 3592 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_q5 : resolveAt exactSites 3628 = some (AXPair.relocate 3592 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_q6 : resolveAt exactSites 3629 = some (AXPair.relocate 3592 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_q7 : resolveAt exactSites 3630 = some (AXPair.relocate 3592 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_q8 : resolveAt exactSites 3631 = some (AXPair.relocate 3592 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_q9 : resolveAt exactSites 3632 = some (AXPair.relocate 3592 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3612_q : AXPair.Bound exactSites 3592 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3612_q0
  · exact row3612_q1
  · exact row3612_q2
  · exact row3612_q3
  · exact row3612_q4
  · exact row3612_q5
  · exact row3612_q6
  · exact row3612_q7
  · exact row3612_q8
  · exact row3612_q9
private theorem row3612_m0 : resolveAt exactSites 3633 = some (AXTimes4.expected 3633 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_m1 : resolveAt exactSites 3634 = some (AXTimes4.expected 3633 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_m2 : resolveAt exactSites 3635 = some (AXTimes4.expected 3633 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_m3 : resolveAt exactSites 3636 = some (AXTimes4.expected 3633 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_m4 : resolveAt exactSites 3637 = some (AXTimes4.expected 3633 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3612_m5 : resolveAt exactSites 3638 = some (AXTimes4.expected 3633 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3612_m : AXTimes4.Bound exactSites 3633 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3612_m0
  · exact row3612_m1
  · exact row3612_m2
  · exact row3612_m3
  · exact row3612_m4
  · exact row3612_m5
theorem block3612 : AXMacro.Realizes exactSites .cons 3612 3639 :=
  AXMacro.cons_realizes bound3612_u bound3612_q bound3612_m
private theorem row3639_u0 : resolveAt exactSites 3639 = some (UnpairPartial.expected 3639 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_u1 : resolveAt exactSites 3640 = some (UnpairPartial.expected 3639 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_u2 : resolveAt exactSites 3641 = some (UnpairPartial.expected 3639 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_u3 : resolveAt exactSites 3642 = some (UnpairPartial.expected 3639 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_u4 : resolveAt exactSites 3643 = some (UnpairPartial.expected 3639 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_u5 : resolveAt exactSites 3644 = some (UnpairPartial.expected 3639 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_u6 : resolveAt exactSites 3645 = some (UnpairPartial.expected 3639 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_u7 : resolveAt exactSites 3646 = some (UnpairPartial.expected 3639 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_u8 : resolveAt exactSites 3647 = some (UnpairPartial.expected 3639 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_u9 : resolveAt exactSites 3648 = some (UnpairPartial.expected 3639 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_u10 : resolveAt exactSites 3649 = some (UnpairPartial.expected 3639 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3639_u : UnpairPartial.Bound exactSites 3639 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3639_u0
  · exact row3639_u1
  · exact row3639_u2
  · exact row3639_u3
  · exact row3639_u4
  · exact row3639_u5
  · exact row3639_u6
  · exact row3639_u7
  · exact row3639_u8
  · exact row3639_u9
  · exact row3639_u10
private theorem row3639_q0 : resolveAt exactSites 3650 = some (AXPair.relocate 3619 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_q1 : resolveAt exactSites 3651 = some (AXPair.relocate 3619 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_q2 : resolveAt exactSites 3652 = some (AXPair.relocate 3619 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_q3 : resolveAt exactSites 3653 = some (AXPair.relocate 3619 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_q4 : resolveAt exactSites 3654 = some (AXPair.relocate 3619 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_q5 : resolveAt exactSites 3655 = some (AXPair.relocate 3619 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_q6 : resolveAt exactSites 3656 = some (AXPair.relocate 3619 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_q7 : resolveAt exactSites 3657 = some (AXPair.relocate 3619 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_q8 : resolveAt exactSites 3658 = some (AXPair.relocate 3619 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_q9 : resolveAt exactSites 3659 = some (AXPair.relocate 3619 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3639_q : AXPair.Bound exactSites 3619 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3639_q0
  · exact row3639_q1
  · exact row3639_q2
  · exact row3639_q3
  · exact row3639_q4
  · exact row3639_q5
  · exact row3639_q6
  · exact row3639_q7
  · exact row3639_q8
  · exact row3639_q9
private theorem row3639_m0 : resolveAt exactSites 3660 = some (AXTimes4.expected 3660 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_m1 : resolveAt exactSites 3661 = some (AXTimes4.expected 3660 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_m2 : resolveAt exactSites 3662 = some (AXTimes4.expected 3660 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_m3 : resolveAt exactSites 3663 = some (AXTimes4.expected 3660 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_m4 : resolveAt exactSites 3664 = some (AXTimes4.expected 3660 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3639_m5 : resolveAt exactSites 3665 = some (AXTimes4.expected 3660 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3639_m : AXTimes4.Bound exactSites 3660 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3639_m0
  · exact row3639_m1
  · exact row3639_m2
  · exact row3639_m3
  · exact row3639_m4
  · exact row3639_m5
theorem block3639 : AXMacro.Realizes exactSites .cons 3639 3666 :=
  AXMacro.cons_realizes bound3639_u bound3639_q bound3639_m
private theorem row3666_u0 : resolveAt exactSites 3666 = some (UnpairPartial.expected 3666 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_u1 : resolveAt exactSites 3667 = some (UnpairPartial.expected 3666 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_u2 : resolveAt exactSites 3668 = some (UnpairPartial.expected 3666 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_u3 : resolveAt exactSites 3669 = some (UnpairPartial.expected 3666 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_u4 : resolveAt exactSites 3670 = some (UnpairPartial.expected 3666 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_u5 : resolveAt exactSites 3671 = some (UnpairPartial.expected 3666 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_u6 : resolveAt exactSites 3672 = some (UnpairPartial.expected 3666 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_u7 : resolveAt exactSites 3673 = some (UnpairPartial.expected 3666 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_u8 : resolveAt exactSites 3674 = some (UnpairPartial.expected 3666 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_u9 : resolveAt exactSites 3675 = some (UnpairPartial.expected 3666 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_u10 : resolveAt exactSites 3676 = some (UnpairPartial.expected 3666 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3666_u : UnpairPartial.Bound exactSites 3666 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3666_u0
  · exact row3666_u1
  · exact row3666_u2
  · exact row3666_u3
  · exact row3666_u4
  · exact row3666_u5
  · exact row3666_u6
  · exact row3666_u7
  · exact row3666_u8
  · exact row3666_u9
  · exact row3666_u10
private theorem row3666_q0 : resolveAt exactSites 3677 = some (AXPair.relocate 3646 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_q1 : resolveAt exactSites 3678 = some (AXPair.relocate 3646 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_q2 : resolveAt exactSites 3679 = some (AXPair.relocate 3646 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_q3 : resolveAt exactSites 3680 = some (AXPair.relocate 3646 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_q4 : resolveAt exactSites 3681 = some (AXPair.relocate 3646 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_q5 : resolveAt exactSites 3682 = some (AXPair.relocate 3646 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_q6 : resolveAt exactSites 3683 = some (AXPair.relocate 3646 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_q7 : resolveAt exactSites 3684 = some (AXPair.relocate 3646 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_q8 : resolveAt exactSites 3685 = some (AXPair.relocate 3646 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_q9 : resolveAt exactSites 3686 = some (AXPair.relocate 3646 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3666_q : AXPair.Bound exactSites 3646 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3666_q0
  · exact row3666_q1
  · exact row3666_q2
  · exact row3666_q3
  · exact row3666_q4
  · exact row3666_q5
  · exact row3666_q6
  · exact row3666_q7
  · exact row3666_q8
  · exact row3666_q9
private theorem row3666_m0 : resolveAt exactSites 3687 = some (AXTimes4.expected 3687 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_m1 : resolveAt exactSites 3688 = some (AXTimes4.expected 3687 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_m2 : resolveAt exactSites 3689 = some (AXTimes4.expected 3687 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_m3 : resolveAt exactSites 3690 = some (AXTimes4.expected 3687 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_m4 : resolveAt exactSites 3691 = some (AXTimes4.expected 3687 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3666_m5 : resolveAt exactSites 3692 = some (AXTimes4.expected 3687 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3666_m : AXTimes4.Bound exactSites 3687 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3666_m0
  · exact row3666_m1
  · exact row3666_m2
  · exact row3666_m3
  · exact row3666_m4
  · exact row3666_m5
theorem block3666 : AXMacro.Realizes exactSites .cons 3666 3693 :=
  AXMacro.cons_realizes bound3666_u bound3666_q bound3666_m
private theorem row3693_i0 : resolveAt exactSites 3693 = some (Instruction.inc 1 (some 3694)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block3693 : AXMacro.Realizes exactSites .incT 3693 3694 :=
  AXMacro.inc_realizes row3693_i0
private theorem row3694_i0 : resolveAt exactSites 3694 = some (Instruction.inc 1 (some 3695)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block3694 : AXMacro.Realizes exactSites .incT 3694 3695 :=
  AXMacro.inc_realizes row3694_i0
private theorem row3695_u0 : resolveAt exactSites 3695 = some (UnpairPartial.expected 3695 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_u1 : resolveAt exactSites 3696 = some (UnpairPartial.expected 3695 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_u2 : resolveAt exactSites 3697 = some (UnpairPartial.expected 3695 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_u3 : resolveAt exactSites 3698 = some (UnpairPartial.expected 3695 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_u4 : resolveAt exactSites 3699 = some (UnpairPartial.expected 3695 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_u5 : resolveAt exactSites 3700 = some (UnpairPartial.expected 3695 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_u6 : resolveAt exactSites 3701 = some (UnpairPartial.expected 3695 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_u7 : resolveAt exactSites 3702 = some (UnpairPartial.expected 3695 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_u8 : resolveAt exactSites 3703 = some (UnpairPartial.expected 3695 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_u9 : resolveAt exactSites 3704 = some (UnpairPartial.expected 3695 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_u10 : resolveAt exactSites 3705 = some (UnpairPartial.expected 3695 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3695_u : UnpairPartial.Bound exactSites 3695 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3695_u0
  · exact row3695_u1
  · exact row3695_u2
  · exact row3695_u3
  · exact row3695_u4
  · exact row3695_u5
  · exact row3695_u6
  · exact row3695_u7
  · exact row3695_u8
  · exact row3695_u9
  · exact row3695_u10
private theorem row3695_q0 : resolveAt exactSites 3706 = some (AXPair.relocate 3675 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_q1 : resolveAt exactSites 3707 = some (AXPair.relocate 3675 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_q2 : resolveAt exactSites 3708 = some (AXPair.relocate 3675 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_q3 : resolveAt exactSites 3709 = some (AXPair.relocate 3675 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_q4 : resolveAt exactSites 3710 = some (AXPair.relocate 3675 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_q5 : resolveAt exactSites 3711 = some (AXPair.relocate 3675 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_q6 : resolveAt exactSites 3712 = some (AXPair.relocate 3675 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_q7 : resolveAt exactSites 3713 = some (AXPair.relocate 3675 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_q8 : resolveAt exactSites 3714 = some (AXPair.relocate 3675 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_q9 : resolveAt exactSites 3715 = some (AXPair.relocate 3675 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3695_q : AXPair.Bound exactSites 3675 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3695_q0
  · exact row3695_q1
  · exact row3695_q2
  · exact row3695_q3
  · exact row3695_q4
  · exact row3695_q5
  · exact row3695_q6
  · exact row3695_q7
  · exact row3695_q8
  · exact row3695_q9
private theorem row3695_m0 : resolveAt exactSites 3716 = some (AXTimes4.expected 3716 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_m1 : resolveAt exactSites 3717 = some (AXTimes4.expected 3716 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_m2 : resolveAt exactSites 3718 = some (AXTimes4.expected 3716 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_m3 : resolveAt exactSites 3719 = some (AXTimes4.expected 3716 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_m4 : resolveAt exactSites 3720 = some (AXTimes4.expected 3716 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3695_m5 : resolveAt exactSites 3721 = some (AXTimes4.expected 3716 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3695_m : AXTimes4.Bound exactSites 3716 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3695_m0
  · exact row3695_m1
  · exact row3695_m2
  · exact row3695_m3
  · exact row3695_m4
  · exact row3695_m5
theorem block3695 : AXMacro.Realizes exactSites .cons 3695 3722 :=
  AXMacro.cons_realizes bound3695_u bound3695_q bound3695_m
private theorem row3722_p0 : resolveAt exactSites 3722 = some (AXPushParam.relocate 3697 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p1 : resolveAt exactSites 3723 = some (AXPushParam.relocate 3697 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p2 : resolveAt exactSites 3724 = some (AXPushParam.relocate 3697 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p3 : resolveAt exactSites 3725 = some (AXPushParam.relocate 3697 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p4 : resolveAt exactSites 3726 = some (AXPushParam.relocate 3697 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p5 : resolveAt exactSites 3727 = some (AXPushParam.relocate 3697 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p6 : resolveAt exactSites 3728 = some (AXPushParam.relocate 3697 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p7 : resolveAt exactSites 3729 = some (AXPushParam.relocate 3697 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p8 : resolveAt exactSites 3730 = some (AXPushParam.relocate 3697 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p9 : resolveAt exactSites 3731 = some (AXPushParam.relocate 3697 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p10 : resolveAt exactSites 3732 = some (AXPushParam.relocate 3697 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p11 : resolveAt exactSites 3733 = some (AXPushParam.relocate 3697 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p12 : resolveAt exactSites 3734 = some (AXPushParam.relocate 3697 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p13 : resolveAt exactSites 3735 = some (AXPushParam.relocate 3697 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p14 : resolveAt exactSites 3736 = some (AXPushParam.relocate 3697 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p15 : resolveAt exactSites 3737 = some (AXPushParam.relocate 3697 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p16 : resolveAt exactSites 3738 = some (AXPushParam.relocate 3697 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p17 : resolveAt exactSites 3739 = some (AXPushParam.relocate 3697 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3722_p18 : resolveAt exactSites 3740 = some (AXPushParam.relocate 3697 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3722_p : AXPushParam.Bound exactSites 3697 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3722_p0
  · exact row3722_p1
  · exact row3722_p2
  · exact row3722_p3
  · exact row3722_p4
  · exact row3722_p5
  · exact row3722_p6
  · exact row3722_p7
  · exact row3722_p8
  · exact row3722_p9
  · exact row3722_p10
  · exact row3722_p11
  · exact row3722_p12
  · exact row3722_p13
  · exact row3722_p14
  · exact row3722_p15
  · exact row3722_p16
  · exact row3722_p17
  · exact row3722_p18
theorem block3722 : AXMacro.Realizes exactSites .push 3722 3741 :=
  AXMacro.push_realizes bound3722_p
private theorem row3741_i0 : resolveAt exactSites 3741 = some (Instruction.inc 1 (some 3742)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block3741 : AXMacro.Realizes exactSites .incT 3741 3742 :=
  AXMacro.inc_realizes row3741_i0
private theorem row3742_u0 : resolveAt exactSites 3742 = some (UnpairPartial.expected 3742 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_u1 : resolveAt exactSites 3743 = some (UnpairPartial.expected 3742 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_u2 : resolveAt exactSites 3744 = some (UnpairPartial.expected 3742 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_u3 : resolveAt exactSites 3745 = some (UnpairPartial.expected 3742 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_u4 : resolveAt exactSites 3746 = some (UnpairPartial.expected 3742 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_u5 : resolveAt exactSites 3747 = some (UnpairPartial.expected 3742 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_u6 : resolveAt exactSites 3748 = some (UnpairPartial.expected 3742 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_u7 : resolveAt exactSites 3749 = some (UnpairPartial.expected 3742 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_u8 : resolveAt exactSites 3750 = some (UnpairPartial.expected 3742 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_u9 : resolveAt exactSites 3751 = some (UnpairPartial.expected 3742 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_u10 : resolveAt exactSites 3752 = some (UnpairPartial.expected 3742 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3742_u : UnpairPartial.Bound exactSites 3742 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3742_u0
  · exact row3742_u1
  · exact row3742_u2
  · exact row3742_u3
  · exact row3742_u4
  · exact row3742_u5
  · exact row3742_u6
  · exact row3742_u7
  · exact row3742_u8
  · exact row3742_u9
  · exact row3742_u10
private theorem row3742_q0 : resolveAt exactSites 3753 = some (AXPair.relocate 3722 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_q1 : resolveAt exactSites 3754 = some (AXPair.relocate 3722 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_q2 : resolveAt exactSites 3755 = some (AXPair.relocate 3722 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_q3 : resolveAt exactSites 3756 = some (AXPair.relocate 3722 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_q4 : resolveAt exactSites 3757 = some (AXPair.relocate 3722 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_q5 : resolveAt exactSites 3758 = some (AXPair.relocate 3722 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_q6 : resolveAt exactSites 3759 = some (AXPair.relocate 3722 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_q7 : resolveAt exactSites 3760 = some (AXPair.relocate 3722 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_q8 : resolveAt exactSites 3761 = some (AXPair.relocate 3722 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_q9 : resolveAt exactSites 3762 = some (AXPair.relocate 3722 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3742_q : AXPair.Bound exactSites 3722 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3742_q0
  · exact row3742_q1
  · exact row3742_q2
  · exact row3742_q3
  · exact row3742_q4
  · exact row3742_q5
  · exact row3742_q6
  · exact row3742_q7
  · exact row3742_q8
  · exact row3742_q9
private theorem row3742_m0 : resolveAt exactSites 3763 = some (AXTimes4.expected 3763 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_m1 : resolveAt exactSites 3764 = some (AXTimes4.expected 3763 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_m2 : resolveAt exactSites 3765 = some (AXTimes4.expected 3763 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_m3 : resolveAt exactSites 3766 = some (AXTimes4.expected 3763 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_m4 : resolveAt exactSites 3767 = some (AXTimes4.expected 3763 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3742_m5 : resolveAt exactSites 3768 = some (AXTimes4.expected 3763 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3742_m : AXTimes4.Bound exactSites 3763 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3742_m0
  · exact row3742_m1
  · exact row3742_m2
  · exact row3742_m3
  · exact row3742_m4
  · exact row3742_m5
theorem block3742 : AXMacro.Realizes exactSites .cons 3742 3769 :=
  AXMacro.cons_realizes bound3742_u bound3742_q bound3742_m
def code022 : List AXMacro.Op := [.cons,.push,.incT,.cons,.cons,.cons,.incT,.incT,.cons,.push,.incT,.cons]
theorem plan022 : AXMacro.Plan exactSites 3565 3769 code022 :=
  AXMacro.Plan.cons block3565 ( AXMacro.Plan.cons block3592 ( AXMacro.Plan.cons block3611 ( AXMacro.Plan.cons block3612 ( AXMacro.Plan.cons block3639 ( AXMacro.Plan.cons block3666 ( AXMacro.Plan.cons block3693 ( AXMacro.Plan.cons block3694 ( AXMacro.Plan.cons block3695 ( AXMacro.Plan.cons block3722 ( AXMacro.Plan.cons block3741 ( AXMacro.Plan.cons block3742 ( AXMacro.Plan.nil 3769))))))))))))
#print axioms plan022
end M6.Source.AXAll

