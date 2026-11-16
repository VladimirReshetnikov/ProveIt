module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row2539_u0 : resolveAt exactSites 2539 = some (UnpairPartial.expected 2539 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_u1 : resolveAt exactSites 2540 = some (UnpairPartial.expected 2539 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_u2 : resolveAt exactSites 2541 = some (UnpairPartial.expected 2539 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_u3 : resolveAt exactSites 2542 = some (UnpairPartial.expected 2539 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_u4 : resolveAt exactSites 2543 = some (UnpairPartial.expected 2539 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_u5 : resolveAt exactSites 2544 = some (UnpairPartial.expected 2539 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_u6 : resolveAt exactSites 2545 = some (UnpairPartial.expected 2539 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_u7 : resolveAt exactSites 2546 = some (UnpairPartial.expected 2539 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_u8 : resolveAt exactSites 2547 = some (UnpairPartial.expected 2539 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_u9 : resolveAt exactSites 2548 = some (UnpairPartial.expected 2539 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_u10 : resolveAt exactSites 2549 = some (UnpairPartial.expected 2539 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2539_u : UnpairPartial.Bound exactSites 2539 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2539_u0
  · exact row2539_u1
  · exact row2539_u2
  · exact row2539_u3
  · exact row2539_u4
  · exact row2539_u5
  · exact row2539_u6
  · exact row2539_u7
  · exact row2539_u8
  · exact row2539_u9
  · exact row2539_u10
private theorem row2539_q0 : resolveAt exactSites 2550 = some (AXPair.relocate 2519 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_q1 : resolveAt exactSites 2551 = some (AXPair.relocate 2519 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_q2 : resolveAt exactSites 2552 = some (AXPair.relocate 2519 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_q3 : resolveAt exactSites 2553 = some (AXPair.relocate 2519 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_q4 : resolveAt exactSites 2554 = some (AXPair.relocate 2519 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_q5 : resolveAt exactSites 2555 = some (AXPair.relocate 2519 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_q6 : resolveAt exactSites 2556 = some (AXPair.relocate 2519 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_q7 : resolveAt exactSites 2557 = some (AXPair.relocate 2519 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_q8 : resolveAt exactSites 2558 = some (AXPair.relocate 2519 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_q9 : resolveAt exactSites 2559 = some (AXPair.relocate 2519 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2539_q : AXPair.Bound exactSites 2519 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2539_q0
  · exact row2539_q1
  · exact row2539_q2
  · exact row2539_q3
  · exact row2539_q4
  · exact row2539_q5
  · exact row2539_q6
  · exact row2539_q7
  · exact row2539_q8
  · exact row2539_q9
private theorem row2539_m0 : resolveAt exactSites 2560 = some (AXTimes4.expected 2560 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_m1 : resolveAt exactSites 2561 = some (AXTimes4.expected 2560 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_m2 : resolveAt exactSites 2562 = some (AXTimes4.expected 2560 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_m3 : resolveAt exactSites 2563 = some (AXTimes4.expected 2560 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_m4 : resolveAt exactSites 2564 = some (AXTimes4.expected 2560 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2539_m5 : resolveAt exactSites 2565 = some (AXTimes4.expected 2560 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2539_m : AXTimes4.Bound exactSites 2560 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2539_m0
  · exact row2539_m1
  · exact row2539_m2
  · exact row2539_m3
  · exact row2539_m4
  · exact row2539_m5
theorem block2539 : AXMacro.Realizes exactSites .cons 2539 2566 :=
  AXMacro.cons_realizes bound2539_u bound2539_q bound2539_m
private theorem row2566_u0 : resolveAt exactSites 2566 = some (UnpairPartial.expected 2566 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_u1 : resolveAt exactSites 2567 = some (UnpairPartial.expected 2566 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_u2 : resolveAt exactSites 2568 = some (UnpairPartial.expected 2566 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_u3 : resolveAt exactSites 2569 = some (UnpairPartial.expected 2566 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_u4 : resolveAt exactSites 2570 = some (UnpairPartial.expected 2566 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_u5 : resolveAt exactSites 2571 = some (UnpairPartial.expected 2566 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_u6 : resolveAt exactSites 2572 = some (UnpairPartial.expected 2566 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_u7 : resolveAt exactSites 2573 = some (UnpairPartial.expected 2566 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_u8 : resolveAt exactSites 2574 = some (UnpairPartial.expected 2566 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_u9 : resolveAt exactSites 2575 = some (UnpairPartial.expected 2566 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_u10 : resolveAt exactSites 2576 = some (UnpairPartial.expected 2566 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2566_u : UnpairPartial.Bound exactSites 2566 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2566_u0
  · exact row2566_u1
  · exact row2566_u2
  · exact row2566_u3
  · exact row2566_u4
  · exact row2566_u5
  · exact row2566_u6
  · exact row2566_u7
  · exact row2566_u8
  · exact row2566_u9
  · exact row2566_u10
private theorem row2566_q0 : resolveAt exactSites 2577 = some (AXPair.relocate 2546 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_q1 : resolveAt exactSites 2578 = some (AXPair.relocate 2546 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_q2 : resolveAt exactSites 2579 = some (AXPair.relocate 2546 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_q3 : resolveAt exactSites 2580 = some (AXPair.relocate 2546 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_q4 : resolveAt exactSites 2581 = some (AXPair.relocate 2546 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_q5 : resolveAt exactSites 2582 = some (AXPair.relocate 2546 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_q6 : resolveAt exactSites 2583 = some (AXPair.relocate 2546 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_q7 : resolveAt exactSites 2584 = some (AXPair.relocate 2546 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_q8 : resolveAt exactSites 2585 = some (AXPair.relocate 2546 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_q9 : resolveAt exactSites 2586 = some (AXPair.relocate 2546 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2566_q : AXPair.Bound exactSites 2546 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2566_q0
  · exact row2566_q1
  · exact row2566_q2
  · exact row2566_q3
  · exact row2566_q4
  · exact row2566_q5
  · exact row2566_q6
  · exact row2566_q7
  · exact row2566_q8
  · exact row2566_q9
private theorem row2566_m0 : resolveAt exactSites 2587 = some (AXTimes4.expected 2587 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_m1 : resolveAt exactSites 2588 = some (AXTimes4.expected 2587 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_m2 : resolveAt exactSites 2589 = some (AXTimes4.expected 2587 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_m3 : resolveAt exactSites 2590 = some (AXTimes4.expected 2587 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_m4 : resolveAt exactSites 2591 = some (AXTimes4.expected 2587 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2566_m5 : resolveAt exactSites 2592 = some (AXTimes4.expected 2587 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2566_m : AXTimes4.Bound exactSites 2587 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2566_m0
  · exact row2566_m1
  · exact row2566_m2
  · exact row2566_m3
  · exact row2566_m4
  · exact row2566_m5
theorem block2566 : AXMacro.Realizes exactSites .cons 2566 2593 :=
  AXMacro.cons_realizes bound2566_u bound2566_q bound2566_m
private theorem row2593_i0 : resolveAt exactSites 2593 = some (Instruction.inc 1 (some 2594)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block2593 : AXMacro.Realizes exactSites .incT 2593 2594 :=
  AXMacro.inc_realizes row2593_i0
private theorem row2594_i0 : resolveAt exactSites 2594 = some (Instruction.inc 1 (some 2595)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block2594 : AXMacro.Realizes exactSites .incT 2594 2595 :=
  AXMacro.inc_realizes row2594_i0
private theorem row2595_p0 : resolveAt exactSites 2595 = some (AXPushParam.relocate 2570 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p1 : resolveAt exactSites 2596 = some (AXPushParam.relocate 2570 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p2 : resolveAt exactSites 2597 = some (AXPushParam.relocate 2570 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p3 : resolveAt exactSites 2598 = some (AXPushParam.relocate 2570 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p4 : resolveAt exactSites 2599 = some (AXPushParam.relocate 2570 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p5 : resolveAt exactSites 2600 = some (AXPushParam.relocate 2570 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p6 : resolveAt exactSites 2601 = some (AXPushParam.relocate 2570 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p7 : resolveAt exactSites 2602 = some (AXPushParam.relocate 2570 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p8 : resolveAt exactSites 2603 = some (AXPushParam.relocate 2570 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p9 : resolveAt exactSites 2604 = some (AXPushParam.relocate 2570 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p10 : resolveAt exactSites 2605 = some (AXPushParam.relocate 2570 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p11 : resolveAt exactSites 2606 = some (AXPushParam.relocate 2570 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p12 : resolveAt exactSites 2607 = some (AXPushParam.relocate 2570 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p13 : resolveAt exactSites 2608 = some (AXPushParam.relocate 2570 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p14 : resolveAt exactSites 2609 = some (AXPushParam.relocate 2570 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p15 : resolveAt exactSites 2610 = some (AXPushParam.relocate 2570 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p16 : resolveAt exactSites 2611 = some (AXPushParam.relocate 2570 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p17 : resolveAt exactSites 2612 = some (AXPushParam.relocate 2570 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2595_p18 : resolveAt exactSites 2613 = some (AXPushParam.relocate 2570 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2595_p : AXPushParam.Bound exactSites 2570 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2595_p0
  · exact row2595_p1
  · exact row2595_p2
  · exact row2595_p3
  · exact row2595_p4
  · exact row2595_p5
  · exact row2595_p6
  · exact row2595_p7
  · exact row2595_p8
  · exact row2595_p9
  · exact row2595_p10
  · exact row2595_p11
  · exact row2595_p12
  · exact row2595_p13
  · exact row2595_p14
  · exact row2595_p15
  · exact row2595_p16
  · exact row2595_p17
  · exact row2595_p18
theorem block2595 : AXMacro.Realizes exactSites .push 2595 2614 :=
  AXMacro.push_realizes bound2595_p
private theorem row2614_i0 : resolveAt exactSites 2614 = some (Instruction.inc 1 (some 2615)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block2614 : AXMacro.Realizes exactSites .incT 2614 2615 :=
  AXMacro.inc_realizes row2614_i0
private theorem row2615_u0 : resolveAt exactSites 2615 = some (UnpairPartial.expected 2615 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_u1 : resolveAt exactSites 2616 = some (UnpairPartial.expected 2615 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_u2 : resolveAt exactSites 2617 = some (UnpairPartial.expected 2615 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_u3 : resolveAt exactSites 2618 = some (UnpairPartial.expected 2615 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_u4 : resolveAt exactSites 2619 = some (UnpairPartial.expected 2615 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_u5 : resolveAt exactSites 2620 = some (UnpairPartial.expected 2615 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_u6 : resolveAt exactSites 2621 = some (UnpairPartial.expected 2615 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_u7 : resolveAt exactSites 2622 = some (UnpairPartial.expected 2615 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_u8 : resolveAt exactSites 2623 = some (UnpairPartial.expected 2615 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_u9 : resolveAt exactSites 2624 = some (UnpairPartial.expected 2615 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_u10 : resolveAt exactSites 2625 = some (UnpairPartial.expected 2615 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2615_u : UnpairPartial.Bound exactSites 2615 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2615_u0
  · exact row2615_u1
  · exact row2615_u2
  · exact row2615_u3
  · exact row2615_u4
  · exact row2615_u5
  · exact row2615_u6
  · exact row2615_u7
  · exact row2615_u8
  · exact row2615_u9
  · exact row2615_u10
private theorem row2615_q0 : resolveAt exactSites 2626 = some (AXPair.relocate 2595 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_q1 : resolveAt exactSites 2627 = some (AXPair.relocate 2595 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_q2 : resolveAt exactSites 2628 = some (AXPair.relocate 2595 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_q3 : resolveAt exactSites 2629 = some (AXPair.relocate 2595 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_q4 : resolveAt exactSites 2630 = some (AXPair.relocate 2595 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_q5 : resolveAt exactSites 2631 = some (AXPair.relocate 2595 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_q6 : resolveAt exactSites 2632 = some (AXPair.relocate 2595 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_q7 : resolveAt exactSites 2633 = some (AXPair.relocate 2595 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_q8 : resolveAt exactSites 2634 = some (AXPair.relocate 2595 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_q9 : resolveAt exactSites 2635 = some (AXPair.relocate 2595 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2615_q : AXPair.Bound exactSites 2595 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2615_q0
  · exact row2615_q1
  · exact row2615_q2
  · exact row2615_q3
  · exact row2615_q4
  · exact row2615_q5
  · exact row2615_q6
  · exact row2615_q7
  · exact row2615_q8
  · exact row2615_q9
private theorem row2615_m0 : resolveAt exactSites 2636 = some (AXTimes4.expected 2636 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_m1 : resolveAt exactSites 2637 = some (AXTimes4.expected 2636 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_m2 : resolveAt exactSites 2638 = some (AXTimes4.expected 2636 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_m3 : resolveAt exactSites 2639 = some (AXTimes4.expected 2636 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_m4 : resolveAt exactSites 2640 = some (AXTimes4.expected 2636 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2615_m5 : resolveAt exactSites 2641 = some (AXTimes4.expected 2636 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2615_m : AXTimes4.Bound exactSites 2636 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2615_m0
  · exact row2615_m1
  · exact row2615_m2
  · exact row2615_m3
  · exact row2615_m4
  · exact row2615_m5
theorem block2615 : AXMacro.Realizes exactSites .cons 2615 2642 :=
  AXMacro.cons_realizes bound2615_u bound2615_q bound2615_m
private theorem row2642_p0 : resolveAt exactSites 2642 = some (AXPushParam.relocate 2617 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p1 : resolveAt exactSites 2643 = some (AXPushParam.relocate 2617 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p2 : resolveAt exactSites 2644 = some (AXPushParam.relocate 2617 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p3 : resolveAt exactSites 2645 = some (AXPushParam.relocate 2617 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p4 : resolveAt exactSites 2646 = some (AXPushParam.relocate 2617 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p5 : resolveAt exactSites 2647 = some (AXPushParam.relocate 2617 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p6 : resolveAt exactSites 2648 = some (AXPushParam.relocate 2617 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p7 : resolveAt exactSites 2649 = some (AXPushParam.relocate 2617 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p8 : resolveAt exactSites 2650 = some (AXPushParam.relocate 2617 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p9 : resolveAt exactSites 2651 = some (AXPushParam.relocate 2617 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p10 : resolveAt exactSites 2652 = some (AXPushParam.relocate 2617 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p11 : resolveAt exactSites 2653 = some (AXPushParam.relocate 2617 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p12 : resolveAt exactSites 2654 = some (AXPushParam.relocate 2617 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p13 : resolveAt exactSites 2655 = some (AXPushParam.relocate 2617 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p14 : resolveAt exactSites 2656 = some (AXPushParam.relocate 2617 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p15 : resolveAt exactSites 2657 = some (AXPushParam.relocate 2617 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p16 : resolveAt exactSites 2658 = some (AXPushParam.relocate 2617 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p17 : resolveAt exactSites 2659 = some (AXPushParam.relocate 2617 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2642_p18 : resolveAt exactSites 2660 = some (AXPushParam.relocate 2617 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2642_p : AXPushParam.Bound exactSites 2617 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2642_p0
  · exact row2642_p1
  · exact row2642_p2
  · exact row2642_p3
  · exact row2642_p4
  · exact row2642_p5
  · exact row2642_p6
  · exact row2642_p7
  · exact row2642_p8
  · exact row2642_p9
  · exact row2642_p10
  · exact row2642_p11
  · exact row2642_p12
  · exact row2642_p13
  · exact row2642_p14
  · exact row2642_p15
  · exact row2642_p16
  · exact row2642_p17
  · exact row2642_p18
theorem block2642 : AXMacro.Realizes exactSites .push 2642 2661 :=
  AXMacro.push_realizes bound2642_p
private theorem row2661_c0 : resolveAt exactSites 2661 = some (CopyToT.expected 4 2661 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2661_c1 : resolveAt exactSites 2662 = some (CopyToT.expected 4 2661 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2661_c2 : resolveAt exactSites 2663 = some (CopyToT.expected 4 2661 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2661_c3 : resolveAt exactSites 2664 = some (CopyToT.expected 4 2661 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2661_c4 : resolveAt exactSites 2665 = some (CopyToT.expected 4 2661 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2661_c5 : resolveAt exactSites 2666 = some (CopyToT.expected 4 2661 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2661_c6 : resolveAt exactSites 2667 = some (CopyToT.expected 4 2661 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2661_c : CopyToT.Bound exactSites 4 2661 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2661_c0
  · exact row2661_c1
  · exact row2661_c2
  · exact row2661_c3
  · exact row2661_c4
  · exact row2661_c5
  · exact row2661_c6
theorem block2661 : AXMacro.Realizes exactSites .copyD 2661 2668 :=
  AXMacro.copyD_realizes bound2661_c
private theorem row2668_p0 : resolveAt exactSites 2668 = some (AXPushParam.relocate 2643 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p1 : resolveAt exactSites 2669 = some (AXPushParam.relocate 2643 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p2 : resolveAt exactSites 2670 = some (AXPushParam.relocate 2643 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p3 : resolveAt exactSites 2671 = some (AXPushParam.relocate 2643 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p4 : resolveAt exactSites 2672 = some (AXPushParam.relocate 2643 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p5 : resolveAt exactSites 2673 = some (AXPushParam.relocate 2643 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p6 : resolveAt exactSites 2674 = some (AXPushParam.relocate 2643 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p7 : resolveAt exactSites 2675 = some (AXPushParam.relocate 2643 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p8 : resolveAt exactSites 2676 = some (AXPushParam.relocate 2643 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p9 : resolveAt exactSites 2677 = some (AXPushParam.relocate 2643 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p10 : resolveAt exactSites 2678 = some (AXPushParam.relocate 2643 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p11 : resolveAt exactSites 2679 = some (AXPushParam.relocate 2643 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p12 : resolveAt exactSites 2680 = some (AXPushParam.relocate 2643 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p13 : resolveAt exactSites 2681 = some (AXPushParam.relocate 2643 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p14 : resolveAt exactSites 2682 = some (AXPushParam.relocate 2643 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p15 : resolveAt exactSites 2683 = some (AXPushParam.relocate 2643 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p16 : resolveAt exactSites 2684 = some (AXPushParam.relocate 2643 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p17 : resolveAt exactSites 2685 = some (AXPushParam.relocate 2643 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2668_p18 : resolveAt exactSites 2686 = some (AXPushParam.relocate 2643 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2668_p : AXPushParam.Bound exactSites 2643 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2668_p0
  · exact row2668_p1
  · exact row2668_p2
  · exact row2668_p3
  · exact row2668_p4
  · exact row2668_p5
  · exact row2668_p6
  · exact row2668_p7
  · exact row2668_p8
  · exact row2668_p9
  · exact row2668_p10
  · exact row2668_p11
  · exact row2668_p12
  · exact row2668_p13
  · exact row2668_p14
  · exact row2668_p15
  · exact row2668_p16
  · exact row2668_p17
  · exact row2668_p18
theorem block2668 : AXMacro.Realizes exactSites .push 2668 2687 :=
  AXMacro.push_realizes bound2668_p
private theorem row2687_c0 : resolveAt exactSites 2687 = some (CopyToT.expected 5 2687 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2687_c1 : resolveAt exactSites 2688 = some (CopyToT.expected 5 2687 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2687_c2 : resolveAt exactSites 2689 = some (CopyToT.expected 5 2687 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2687_c3 : resolveAt exactSites 2690 = some (CopyToT.expected 5 2687 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2687_c4 : resolveAt exactSites 2691 = some (CopyToT.expected 5 2687 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2687_c5 : resolveAt exactSites 2692 = some (CopyToT.expected 5 2687 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2687_c6 : resolveAt exactSites 2693 = some (CopyToT.expected 5 2687 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2687_c : CopyToT.Bound exactSites 5 2687 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2687_c0
  · exact row2687_c1
  · exact row2687_c2
  · exact row2687_c3
  · exact row2687_c4
  · exact row2687_c5
  · exact row2687_c6
theorem block2687 : AXMacro.Realizes exactSites .copyH 2687 2694 :=
  AXMacro.copyH_realizes bound2687_c
private theorem row2694_u0 : resolveAt exactSites 2694 = some (UnpairPartial.expected 2694 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_u1 : resolveAt exactSites 2695 = some (UnpairPartial.expected 2694 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_u2 : resolveAt exactSites 2696 = some (UnpairPartial.expected 2694 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_u3 : resolveAt exactSites 2697 = some (UnpairPartial.expected 2694 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_u4 : resolveAt exactSites 2698 = some (UnpairPartial.expected 2694 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_u5 : resolveAt exactSites 2699 = some (UnpairPartial.expected 2694 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_u6 : resolveAt exactSites 2700 = some (UnpairPartial.expected 2694 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_u7 : resolveAt exactSites 2701 = some (UnpairPartial.expected 2694 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_u8 : resolveAt exactSites 2702 = some (UnpairPartial.expected 2694 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_u9 : resolveAt exactSites 2703 = some (UnpairPartial.expected 2694 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_u10 : resolveAt exactSites 2704 = some (UnpairPartial.expected 2694 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2694_u : UnpairPartial.Bound exactSites 2694 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2694_u0
  · exact row2694_u1
  · exact row2694_u2
  · exact row2694_u3
  · exact row2694_u4
  · exact row2694_u5
  · exact row2694_u6
  · exact row2694_u7
  · exact row2694_u8
  · exact row2694_u9
  · exact row2694_u10
private theorem row2694_q0 : resolveAt exactSites 2705 = some (AXPair.relocate 2674 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_q1 : resolveAt exactSites 2706 = some (AXPair.relocate 2674 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_q2 : resolveAt exactSites 2707 = some (AXPair.relocate 2674 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_q3 : resolveAt exactSites 2708 = some (AXPair.relocate 2674 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_q4 : resolveAt exactSites 2709 = some (AXPair.relocate 2674 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_q5 : resolveAt exactSites 2710 = some (AXPair.relocate 2674 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_q6 : resolveAt exactSites 2711 = some (AXPair.relocate 2674 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_q7 : resolveAt exactSites 2712 = some (AXPair.relocate 2674 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_q8 : resolveAt exactSites 2713 = some (AXPair.relocate 2674 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_q9 : resolveAt exactSites 2714 = some (AXPair.relocate 2674 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2694_q : AXPair.Bound exactSites 2674 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2694_q0
  · exact row2694_q1
  · exact row2694_q2
  · exact row2694_q3
  · exact row2694_q4
  · exact row2694_q5
  · exact row2694_q6
  · exact row2694_q7
  · exact row2694_q8
  · exact row2694_q9
private theorem row2694_m0 : resolveAt exactSites 2715 = some (AXTimes4.expected 2715 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_m1 : resolveAt exactSites 2716 = some (AXTimes4.expected 2715 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_m2 : resolveAt exactSites 2717 = some (AXTimes4.expected 2715 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_m3 : resolveAt exactSites 2718 = some (AXTimes4.expected 2715 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_m4 : resolveAt exactSites 2719 = some (AXTimes4.expected 2715 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2694_m5 : resolveAt exactSites 2720 = some (AXTimes4.expected 2715 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2694_m : AXTimes4.Bound exactSites 2715 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2694_m0
  · exact row2694_m1
  · exact row2694_m2
  · exact row2694_m3
  · exact row2694_m4
  · exact row2694_m5
theorem block2694 : AXMacro.Realizes exactSites .cons 2694 2721 :=
  AXMacro.cons_realizes bound2694_u bound2694_q bound2694_m
def code016 : List AXMacro.Op := [.cons,.cons,.incT,.incT,.push,.incT,.cons,.push,.copyD,.push,.copyH,.cons]
theorem plan016 : AXMacro.Plan exactSites 2539 2721 code016 :=
  AXMacro.Plan.cons block2539 ( AXMacro.Plan.cons block2566 ( AXMacro.Plan.cons block2593 ( AXMacro.Plan.cons block2594 ( AXMacro.Plan.cons block2595 ( AXMacro.Plan.cons block2614 ( AXMacro.Plan.cons block2615 ( AXMacro.Plan.cons block2642 ( AXMacro.Plan.cons block2661 ( AXMacro.Plan.cons block2668 ( AXMacro.Plan.cons block2687 ( AXMacro.Plan.cons block2694 ( AXMacro.Plan.nil 2721))))))))))))
#print axioms plan016
end M6.Source.AXAll

