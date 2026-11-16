module
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row559_i0 : resolveAt exactSites 559 = some (Instruction.inc 1 (some 560)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem block559 : AXMacro.Realizes exactSites .incT 559 560 :=
  AXMacro.inc_realizes row559_i0
private theorem row560_p0 : resolveAt exactSites 560 = some (AXPushParam.relocate 535 (AXPushParam.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p1 : resolveAt exactSites 561 = some (AXPushParam.relocate 535 (AXPushParam.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p2 : resolveAt exactSites 562 = some (AXPushParam.relocate 535 (AXPushParam.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p3 : resolveAt exactSites 563 = some (AXPushParam.relocate 535 (AXPushParam.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p4 : resolveAt exactSites 564 = some (AXPushParam.relocate 535 (AXPushParam.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p5 : resolveAt exactSites 565 = some (AXPushParam.relocate 535 (AXPushParam.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p6 : resolveAt exactSites 566 = some (AXPushParam.relocate 535 (AXPushParam.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p7 : resolveAt exactSites 567 = some (AXPushParam.relocate 535 (AXPushParam.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p8 : resolveAt exactSites 568 = some (AXPushParam.relocate 535 (AXPushParam.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p9 : resolveAt exactSites 569 = some (AXPushParam.relocate 535 (AXPushParam.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p10 : resolveAt exactSites 570 = some (AXPushParam.relocate 535 (AXPushParam.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p11 : resolveAt exactSites 571 = some (AXPushParam.relocate 535 (AXPushParam.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p12 : resolveAt exactSites 572 = some (AXPushParam.relocate 535 (AXPushParam.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p13 : resolveAt exactSites 573 = some (AXPushParam.relocate 535 (AXPushParam.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p14 : resolveAt exactSites 574 = some (AXPushParam.relocate 535 (AXPushParam.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p15 : resolveAt exactSites 575 = some (AXPushParam.relocate 535 (AXPushParam.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p16 : resolveAt exactSites 576 = some (AXPushParam.relocate 535 (AXPushParam.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p17 : resolveAt exactSites 577 = some (AXPushParam.relocate 535 (AXPushParam.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row560_p18 : resolveAt exactSites 578 = some (AXPushParam.relocate 535 (AXPushParam.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound560_p : AXPushParam.Bound exactSites 535 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row560_p0
  · exact row560_p1
  · exact row560_p2
  · exact row560_p3
  · exact row560_p4
  · exact row560_p5
  · exact row560_p6
  · exact row560_p7
  · exact row560_p8
  · exact row560_p9
  · exact row560_p10
  · exact row560_p11
  · exact row560_p12
  · exact row560_p13
  · exact row560_p14
  · exact row560_p15
  · exact row560_p16
  · exact row560_p17
  · exact row560_p18
theorem block560 : AXMacro.Realizes exactSites .push 560 579 :=
  AXMacro.push_realizes bound560_p
private theorem row579_c0 : resolveAt exactSites 579 = some (CopyToT.expected 3 579 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row579_c1 : resolveAt exactSites 580 = some (CopyToT.expected 3 579 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row579_c2 : resolveAt exactSites 581 = some (CopyToT.expected 3 579 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row579_c3 : resolveAt exactSites 582 = some (CopyToT.expected 3 579 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row579_c4 : resolveAt exactSites 583 = some (CopyToT.expected 3 579 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row579_c5 : resolveAt exactSites 584 = some (CopyToT.expected 3 579 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row579_c6 : resolveAt exactSites 585 = some (CopyToT.expected 3 579 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound579_c : CopyToT.Bound exactSites 3 579 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row579_c0
  · exact row579_c1
  · exact row579_c2
  · exact row579_c3
  · exact row579_c4
  · exact row579_c5
  · exact row579_c6
theorem block579 : AXMacro.Realizes exactSites .copyA 579 586 :=
  AXMacro.copyA_realizes bound579_c
private theorem row586_p0 : resolveAt exactSites 586 = some (AXPushParam.relocate 561 (AXPushParam.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p1 : resolveAt exactSites 587 = some (AXPushParam.relocate 561 (AXPushParam.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p2 : resolveAt exactSites 588 = some (AXPushParam.relocate 561 (AXPushParam.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p3 : resolveAt exactSites 589 = some (AXPushParam.relocate 561 (AXPushParam.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p4 : resolveAt exactSites 590 = some (AXPushParam.relocate 561 (AXPushParam.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p5 : resolveAt exactSites 591 = some (AXPushParam.relocate 561 (AXPushParam.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p6 : resolveAt exactSites 592 = some (AXPushParam.relocate 561 (AXPushParam.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p7 : resolveAt exactSites 593 = some (AXPushParam.relocate 561 (AXPushParam.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p8 : resolveAt exactSites 594 = some (AXPushParam.relocate 561 (AXPushParam.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p9 : resolveAt exactSites 595 = some (AXPushParam.relocate 561 (AXPushParam.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p10 : resolveAt exactSites 596 = some (AXPushParam.relocate 561 (AXPushParam.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p11 : resolveAt exactSites 597 = some (AXPushParam.relocate 561 (AXPushParam.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p12 : resolveAt exactSites 598 = some (AXPushParam.relocate 561 (AXPushParam.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p13 : resolveAt exactSites 599 = some (AXPushParam.relocate 561 (AXPushParam.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p14 : resolveAt exactSites 600 = some (AXPushParam.relocate 561 (AXPushParam.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p15 : resolveAt exactSites 601 = some (AXPushParam.relocate 561 (AXPushParam.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p16 : resolveAt exactSites 602 = some (AXPushParam.relocate 561 (AXPushParam.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p17 : resolveAt exactSites 603 = some (AXPushParam.relocate 561 (AXPushParam.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row586_p18 : resolveAt exactSites 604 = some (AXPushParam.relocate 561 (AXPushParam.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound586_p : AXPushParam.Bound exactSites 561 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row586_p0
  · exact row586_p1
  · exact row586_p2
  · exact row586_p3
  · exact row586_p4
  · exact row586_p5
  · exact row586_p6
  · exact row586_p7
  · exact row586_p8
  · exact row586_p9
  · exact row586_p10
  · exact row586_p11
  · exact row586_p12
  · exact row586_p13
  · exact row586_p14
  · exact row586_p15
  · exact row586_p16
  · exact row586_p17
  · exact row586_p18
theorem block586 : AXMacro.Realizes exactSites .push 586 605 :=
  AXMacro.push_realizes bound586_p
private theorem row605_c0 : resolveAt exactSites 605 = some (CopyToT.expected 5 605 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row605_c1 : resolveAt exactSites 606 = some (CopyToT.expected 5 605 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row605_c2 : resolveAt exactSites 607 = some (CopyToT.expected 5 605 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row605_c3 : resolveAt exactSites 608 = some (CopyToT.expected 5 605 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row605_c4 : resolveAt exactSites 609 = some (CopyToT.expected 5 605 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row605_c5 : resolveAt exactSites 610 = some (CopyToT.expected 5 605 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row605_c6 : resolveAt exactSites 611 = some (CopyToT.expected 5 605 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound605_c : CopyToT.Bound exactSites 5 605 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row605_c0
  · exact row605_c1
  · exact row605_c2
  · exact row605_c3
  · exact row605_c4
  · exact row605_c5
  · exact row605_c6
theorem block605 : AXMacro.Realizes exactSites .copyH 605 612 :=
  AXMacro.copyH_realizes bound605_c
private theorem row612_u0 : resolveAt exactSites 612 = some (UnpairPartial.expected 612 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_u1 : resolveAt exactSites 613 = some (UnpairPartial.expected 612 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_u2 : resolveAt exactSites 614 = some (UnpairPartial.expected 612 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_u3 : resolveAt exactSites 615 = some (UnpairPartial.expected 612 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_u4 : resolveAt exactSites 616 = some (UnpairPartial.expected 612 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_u5 : resolveAt exactSites 617 = some (UnpairPartial.expected 612 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_u6 : resolveAt exactSites 618 = some (UnpairPartial.expected 612 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_u7 : resolveAt exactSites 619 = some (UnpairPartial.expected 612 7) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_u8 : resolveAt exactSites 620 = some (UnpairPartial.expected 612 8) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_u9 : resolveAt exactSites 621 = some (UnpairPartial.expected 612 9) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_u10 : resolveAt exactSites 622 = some (UnpairPartial.expected 612 10) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound612_u : UnpairPartial.Bound exactSites 612 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row612_u0
  · exact row612_u1
  · exact row612_u2
  · exact row612_u3
  · exact row612_u4
  · exact row612_u5
  · exact row612_u6
  · exact row612_u7
  · exact row612_u8
  · exact row612_u9
  · exact row612_u10
private theorem row612_q0 : resolveAt exactSites 623 = some (AXPair.relocate 592 (AXPair.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_q1 : resolveAt exactSites 624 = some (AXPair.relocate 592 (AXPair.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_q2 : resolveAt exactSites 625 = some (AXPair.relocate 592 (AXPair.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_q3 : resolveAt exactSites 626 = some (AXPair.relocate 592 (AXPair.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_q4 : resolveAt exactSites 627 = some (AXPair.relocate 592 (AXPair.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_q5 : resolveAt exactSites 628 = some (AXPair.relocate 592 (AXPair.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_q6 : resolveAt exactSites 629 = some (AXPair.relocate 592 (AXPair.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_q7 : resolveAt exactSites 630 = some (AXPair.relocate 592 (AXPair.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_q8 : resolveAt exactSites 631 = some (AXPair.relocate 592 (AXPair.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_q9 : resolveAt exactSites 632 = some (AXPair.relocate 592 (AXPair.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound612_q : AXPair.Bound exactSites 592 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row612_q0
  · exact row612_q1
  · exact row612_q2
  · exact row612_q3
  · exact row612_q4
  · exact row612_q5
  · exact row612_q6
  · exact row612_q7
  · exact row612_q8
  · exact row612_q9
private theorem row612_m0 : resolveAt exactSites 633 = some (AXTimes4.expected 633 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_m1 : resolveAt exactSites 634 = some (AXTimes4.expected 633 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_m2 : resolveAt exactSites 635 = some (AXTimes4.expected 633 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_m3 : resolveAt exactSites 636 = some (AXTimes4.expected 633 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_m4 : resolveAt exactSites 637 = some (AXTimes4.expected 633 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row612_m5 : resolveAt exactSites 638 = some (AXTimes4.expected 633 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound612_m : AXTimes4.Bound exactSites 633 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row612_m0
  · exact row612_m1
  · exact row612_m2
  · exact row612_m3
  · exact row612_m4
  · exact row612_m5
theorem block612 : AXMacro.Realizes exactSites .cons 612 639 :=
  AXMacro.cons_realizes bound612_u bound612_q bound612_m
private theorem row639_i0 : resolveAt exactSites 639 = some (Instruction.inc 1 (some 640)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem block639 : AXMacro.Realizes exactSites .incT 639 640 :=
  AXMacro.inc_realizes row639_i0
private theorem row640_i0 : resolveAt exactSites 640 = some (Instruction.inc 1 (some 641)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem block640 : AXMacro.Realizes exactSites .incT 640 641 :=
  AXMacro.inc_realizes row640_i0
private theorem row641_i0 : resolveAt exactSites 641 = some (Instruction.inc 1 (some 642)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem block641 : AXMacro.Realizes exactSites .incT 641 642 :=
  AXMacro.inc_realizes row641_i0
private theorem row642_p0 : resolveAt exactSites 642 = some (AXPushParam.relocate 617 (AXPushParam.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p1 : resolveAt exactSites 643 = some (AXPushParam.relocate 617 (AXPushParam.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p2 : resolveAt exactSites 644 = some (AXPushParam.relocate 617 (AXPushParam.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p3 : resolveAt exactSites 645 = some (AXPushParam.relocate 617 (AXPushParam.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p4 : resolveAt exactSites 646 = some (AXPushParam.relocate 617 (AXPushParam.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p5 : resolveAt exactSites 647 = some (AXPushParam.relocate 617 (AXPushParam.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p6 : resolveAt exactSites 648 = some (AXPushParam.relocate 617 (AXPushParam.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p7 : resolveAt exactSites 649 = some (AXPushParam.relocate 617 (AXPushParam.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p8 : resolveAt exactSites 650 = some (AXPushParam.relocate 617 (AXPushParam.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p9 : resolveAt exactSites 651 = some (AXPushParam.relocate 617 (AXPushParam.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p10 : resolveAt exactSites 652 = some (AXPushParam.relocate 617 (AXPushParam.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p11 : resolveAt exactSites 653 = some (AXPushParam.relocate 617 (AXPushParam.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p12 : resolveAt exactSites 654 = some (AXPushParam.relocate 617 (AXPushParam.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p13 : resolveAt exactSites 655 = some (AXPushParam.relocate 617 (AXPushParam.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p14 : resolveAt exactSites 656 = some (AXPushParam.relocate 617 (AXPushParam.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p15 : resolveAt exactSites 657 = some (AXPushParam.relocate 617 (AXPushParam.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p16 : resolveAt exactSites 658 = some (AXPushParam.relocate 617 (AXPushParam.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p17 : resolveAt exactSites 659 = some (AXPushParam.relocate 617 (AXPushParam.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row642_p18 : resolveAt exactSites 660 = some (AXPushParam.relocate 617 (AXPushParam.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound642_p : AXPushParam.Bound exactSites 617 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row642_p0
  · exact row642_p1
  · exact row642_p2
  · exact row642_p3
  · exact row642_p4
  · exact row642_p5
  · exact row642_p6
  · exact row642_p7
  · exact row642_p8
  · exact row642_p9
  · exact row642_p10
  · exact row642_p11
  · exact row642_p12
  · exact row642_p13
  · exact row642_p14
  · exact row642_p15
  · exact row642_p16
  · exact row642_p17
  · exact row642_p18
theorem block642 : AXMacro.Realizes exactSites .push 642 661 :=
  AXMacro.push_realizes bound642_p
private theorem row661_c0 : resolveAt exactSites 661 = some (CopyToT.expected 4 661 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row661_c1 : resolveAt exactSites 662 = some (CopyToT.expected 4 661 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row661_c2 : resolveAt exactSites 663 = some (CopyToT.expected 4 661 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row661_c3 : resolveAt exactSites 664 = some (CopyToT.expected 4 661 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row661_c4 : resolveAt exactSites 665 = some (CopyToT.expected 4 661 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row661_c5 : resolveAt exactSites 666 = some (CopyToT.expected 4 661 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row661_c6 : resolveAt exactSites 667 = some (CopyToT.expected 4 661 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound661_c : CopyToT.Bound exactSites 4 661 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row661_c0
  · exact row661_c1
  · exact row661_c2
  · exact row661_c3
  · exact row661_c4
  · exact row661_c5
  · exact row661_c6
theorem block661 : AXMacro.Realizes exactSites .copyD 661 668 :=
  AXMacro.copyD_realizes bound661_c
private theorem row668_p0 : resolveAt exactSites 668 = some (AXPushParam.relocate 643 (AXPushParam.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p1 : resolveAt exactSites 669 = some (AXPushParam.relocate 643 (AXPushParam.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p2 : resolveAt exactSites 670 = some (AXPushParam.relocate 643 (AXPushParam.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p3 : resolveAt exactSites 671 = some (AXPushParam.relocate 643 (AXPushParam.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p4 : resolveAt exactSites 672 = some (AXPushParam.relocate 643 (AXPushParam.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p5 : resolveAt exactSites 673 = some (AXPushParam.relocate 643 (AXPushParam.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p6 : resolveAt exactSites 674 = some (AXPushParam.relocate 643 (AXPushParam.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p7 : resolveAt exactSites 675 = some (AXPushParam.relocate 643 (AXPushParam.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p8 : resolveAt exactSites 676 = some (AXPushParam.relocate 643 (AXPushParam.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p9 : resolveAt exactSites 677 = some (AXPushParam.relocate 643 (AXPushParam.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p10 : resolveAt exactSites 678 = some (AXPushParam.relocate 643 (AXPushParam.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p11 : resolveAt exactSites 679 = some (AXPushParam.relocate 643 (AXPushParam.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p12 : resolveAt exactSites 680 = some (AXPushParam.relocate 643 (AXPushParam.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p13 : resolveAt exactSites 681 = some (AXPushParam.relocate 643 (AXPushParam.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p14 : resolveAt exactSites 682 = some (AXPushParam.relocate 643 (AXPushParam.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p15 : resolveAt exactSites 683 = some (AXPushParam.relocate 643 (AXPushParam.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p16 : resolveAt exactSites 684 = some (AXPushParam.relocate 643 (AXPushParam.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p17 : resolveAt exactSites 685 = some (AXPushParam.relocate 643 (AXPushParam.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row668_p18 : resolveAt exactSites 686 = some (AXPushParam.relocate 643 (AXPushParam.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound668_p : AXPushParam.Bound exactSites 643 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row668_p0
  · exact row668_p1
  · exact row668_p2
  · exact row668_p3
  · exact row668_p4
  · exact row668_p5
  · exact row668_p6
  · exact row668_p7
  · exact row668_p8
  · exact row668_p9
  · exact row668_p10
  · exact row668_p11
  · exact row668_p12
  · exact row668_p13
  · exact row668_p14
  · exact row668_p15
  · exact row668_p16
  · exact row668_p17
  · exact row668_p18
theorem block668 : AXMacro.Realizes exactSites .push 668 687 :=
  AXMacro.push_realizes bound668_p
def code003 : List AXMacro.Op := [.incT,.push,.copyA,.push,.copyH,.cons,.incT,.incT,.incT,.push,.copyD,.push]
theorem plan003 : AXMacro.Plan exactSites 559 687 code003 :=
  AXMacro.Plan.cons block559 ( AXMacro.Plan.cons block560 ( AXMacro.Plan.cons block579 ( AXMacro.Plan.cons block586 ( AXMacro.Plan.cons block605 ( AXMacro.Plan.cons block612 ( AXMacro.Plan.cons block639 ( AXMacro.Plan.cons block640 ( AXMacro.Plan.cons block641 ( AXMacro.Plan.cons block642 ( AXMacro.Plan.cons block661 ( AXMacro.Plan.cons block668 ( AXMacro.Plan.nil 687))))))))))))
#print axioms plan003
end M6.Source.AXAll

