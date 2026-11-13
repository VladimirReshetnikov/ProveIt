module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row687_c0 : resolveAt exactSites 687 = some (CopyToT.expected 5 687 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row687_c1 : resolveAt exactSites 688 = some (CopyToT.expected 5 687 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row687_c2 : resolveAt exactSites 689 = some (CopyToT.expected 5 687 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row687_c3 : resolveAt exactSites 690 = some (CopyToT.expected 5 687 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row687_c4 : resolveAt exactSites 691 = some (CopyToT.expected 5 687 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row687_c5 : resolveAt exactSites 692 = some (CopyToT.expected 5 687 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row687_c6 : resolveAt exactSites 693 = some (CopyToT.expected 5 687 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound687_c : CopyToT.Bound exactSites 5 687 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row687_c0
  · exact row687_c1
  · exact row687_c2
  · exact row687_c3
  · exact row687_c4
  · exact row687_c5
  · exact row687_c6
theorem block687 : AXMacro.Realizes exactSites .copyH 687 694 :=
  AXMacro.copyH_realizes bound687_c
private theorem row694_u0 : resolveAt exactSites 694 = some (UnpairPartial.expected 694 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_u1 : resolveAt exactSites 695 = some (UnpairPartial.expected 694 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_u2 : resolveAt exactSites 696 = some (UnpairPartial.expected 694 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_u3 : resolveAt exactSites 697 = some (UnpairPartial.expected 694 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_u4 : resolveAt exactSites 698 = some (UnpairPartial.expected 694 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_u5 : resolveAt exactSites 699 = some (UnpairPartial.expected 694 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_u6 : resolveAt exactSites 700 = some (UnpairPartial.expected 694 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_u7 : resolveAt exactSites 701 = some (UnpairPartial.expected 694 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_u8 : resolveAt exactSites 702 = some (UnpairPartial.expected 694 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_u9 : resolveAt exactSites 703 = some (UnpairPartial.expected 694 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_u10 : resolveAt exactSites 704 = some (UnpairPartial.expected 694 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound694_u : UnpairPartial.Bound exactSites 694 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row694_u0
  · exact row694_u1
  · exact row694_u2
  · exact row694_u3
  · exact row694_u4
  · exact row694_u5
  · exact row694_u6
  · exact row694_u7
  · exact row694_u8
  · exact row694_u9
  · exact row694_u10
private theorem row694_q0 : resolveAt exactSites 705 = some (AXPair.relocate 674 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_q1 : resolveAt exactSites 706 = some (AXPair.relocate 674 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_q2 : resolveAt exactSites 707 = some (AXPair.relocate 674 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_q3 : resolveAt exactSites 708 = some (AXPair.relocate 674 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_q4 : resolveAt exactSites 709 = some (AXPair.relocate 674 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_q5 : resolveAt exactSites 710 = some (AXPair.relocate 674 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_q6 : resolveAt exactSites 711 = some (AXPair.relocate 674 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_q7 : resolveAt exactSites 712 = some (AXPair.relocate 674 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_q8 : resolveAt exactSites 713 = some (AXPair.relocate 674 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_q9 : resolveAt exactSites 714 = some (AXPair.relocate 674 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound694_q : AXPair.Bound exactSites 674 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row694_q0
  · exact row694_q1
  · exact row694_q2
  · exact row694_q3
  · exact row694_q4
  · exact row694_q5
  · exact row694_q6
  · exact row694_q7
  · exact row694_q8
  · exact row694_q9
private theorem row694_m0 : resolveAt exactSites 715 = some (AXTimes4.expected 715 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_m1 : resolveAt exactSites 716 = some (AXTimes4.expected 715 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_m2 : resolveAt exactSites 717 = some (AXTimes4.expected 715 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_m3 : resolveAt exactSites 718 = some (AXTimes4.expected 715 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_m4 : resolveAt exactSites 719 = some (AXTimes4.expected 715 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row694_m5 : resolveAt exactSites 720 = some (AXTimes4.expected 715 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound694_m : AXTimes4.Bound exactSites 715 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row694_m0
  · exact row694_m1
  · exact row694_m2
  · exact row694_m3
  · exact row694_m4
  · exact row694_m5
theorem block694 : AXMacro.Realizes exactSites .cons 694 721 :=
  AXMacro.cons_realizes bound694_u bound694_q bound694_m
private theorem row721_i0 : resolveAt exactSites 721 = some (Instruction.inc 1 (some 722)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block721 : AXMacro.Realizes exactSites .incT 721 722 :=
  AXMacro.inc_realizes row721_i0
private theorem row722_p0 : resolveAt exactSites 722 = some (AXPushParam.relocate 697 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p1 : resolveAt exactSites 723 = some (AXPushParam.relocate 697 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p2 : resolveAt exactSites 724 = some (AXPushParam.relocate 697 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p3 : resolveAt exactSites 725 = some (AXPushParam.relocate 697 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p4 : resolveAt exactSites 726 = some (AXPushParam.relocate 697 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p5 : resolveAt exactSites 727 = some (AXPushParam.relocate 697 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p6 : resolveAt exactSites 728 = some (AXPushParam.relocate 697 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p7 : resolveAt exactSites 729 = some (AXPushParam.relocate 697 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p8 : resolveAt exactSites 730 = some (AXPushParam.relocate 697 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p9 : resolveAt exactSites 731 = some (AXPushParam.relocate 697 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p10 : resolveAt exactSites 732 = some (AXPushParam.relocate 697 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p11 : resolveAt exactSites 733 = some (AXPushParam.relocate 697 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p12 : resolveAt exactSites 734 = some (AXPushParam.relocate 697 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p13 : resolveAt exactSites 735 = some (AXPushParam.relocate 697 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p14 : resolveAt exactSites 736 = some (AXPushParam.relocate 697 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p15 : resolveAt exactSites 737 = some (AXPushParam.relocate 697 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p16 : resolveAt exactSites 738 = some (AXPushParam.relocate 697 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p17 : resolveAt exactSites 739 = some (AXPushParam.relocate 697 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row722_p18 : resolveAt exactSites 740 = some (AXPushParam.relocate 697 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound722_p : AXPushParam.Bound exactSites 697 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row722_p0
  · exact row722_p1
  · exact row722_p2
  · exact row722_p3
  · exact row722_p4
  · exact row722_p5
  · exact row722_p6
  · exact row722_p7
  · exact row722_p8
  · exact row722_p9
  · exact row722_p10
  · exact row722_p11
  · exact row722_p12
  · exact row722_p13
  · exact row722_p14
  · exact row722_p15
  · exact row722_p16
  · exact row722_p17
  · exact row722_p18
theorem block722 : AXMacro.Realizes exactSites .push 722 741 :=
  AXMacro.push_realizes bound722_p
private theorem row741_c0 : resolveAt exactSites 741 = some (CopyToT.expected 4 741 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row741_c1 : resolveAt exactSites 742 = some (CopyToT.expected 4 741 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row741_c2 : resolveAt exactSites 743 = some (CopyToT.expected 4 741 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row741_c3 : resolveAt exactSites 744 = some (CopyToT.expected 4 741 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row741_c4 : resolveAt exactSites 745 = some (CopyToT.expected 4 741 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row741_c5 : resolveAt exactSites 746 = some (CopyToT.expected 4 741 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row741_c6 : resolveAt exactSites 747 = some (CopyToT.expected 4 741 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound741_c : CopyToT.Bound exactSites 4 741 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row741_c0
  · exact row741_c1
  · exact row741_c2
  · exact row741_c3
  · exact row741_c4
  · exact row741_c5
  · exact row741_c6
theorem block741 : AXMacro.Realizes exactSites .copyD 741 748 :=
  AXMacro.copyD_realizes bound741_c
private theorem row748_p0 : resolveAt exactSites 748 = some (AXPushParam.relocate 723 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p1 : resolveAt exactSites 749 = some (AXPushParam.relocate 723 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p2 : resolveAt exactSites 750 = some (AXPushParam.relocate 723 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p3 : resolveAt exactSites 751 = some (AXPushParam.relocate 723 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p4 : resolveAt exactSites 752 = some (AXPushParam.relocate 723 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p5 : resolveAt exactSites 753 = some (AXPushParam.relocate 723 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p6 : resolveAt exactSites 754 = some (AXPushParam.relocate 723 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p7 : resolveAt exactSites 755 = some (AXPushParam.relocate 723 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p8 : resolveAt exactSites 756 = some (AXPushParam.relocate 723 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p9 : resolveAt exactSites 757 = some (AXPushParam.relocate 723 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p10 : resolveAt exactSites 758 = some (AXPushParam.relocate 723 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p11 : resolveAt exactSites 759 = some (AXPushParam.relocate 723 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p12 : resolveAt exactSites 760 = some (AXPushParam.relocate 723 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p13 : resolveAt exactSites 761 = some (AXPushParam.relocate 723 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p14 : resolveAt exactSites 762 = some (AXPushParam.relocate 723 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p15 : resolveAt exactSites 763 = some (AXPushParam.relocate 723 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p16 : resolveAt exactSites 764 = some (AXPushParam.relocate 723 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p17 : resolveAt exactSites 765 = some (AXPushParam.relocate 723 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row748_p18 : resolveAt exactSites 766 = some (AXPushParam.relocate 723 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound748_p : AXPushParam.Bound exactSites 723 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row748_p0
  · exact row748_p1
  · exact row748_p2
  · exact row748_p3
  · exact row748_p4
  · exact row748_p5
  · exact row748_p6
  · exact row748_p7
  · exact row748_p8
  · exact row748_p9
  · exact row748_p10
  · exact row748_p11
  · exact row748_p12
  · exact row748_p13
  · exact row748_p14
  · exact row748_p15
  · exact row748_p16
  · exact row748_p17
  · exact row748_p18
theorem block748 : AXMacro.Realizes exactSites .push 748 767 :=
  AXMacro.push_realizes bound748_p
private theorem row767_c0 : resolveAt exactSites 767 = some (CopyToT.expected 5 767 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row767_c1 : resolveAt exactSites 768 = some (CopyToT.expected 5 767 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row767_c2 : resolveAt exactSites 769 = some (CopyToT.expected 5 767 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row767_c3 : resolveAt exactSites 770 = some (CopyToT.expected 5 767 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row767_c4 : resolveAt exactSites 771 = some (CopyToT.expected 5 767 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row767_c5 : resolveAt exactSites 772 = some (CopyToT.expected 5 767 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row767_c6 : resolveAt exactSites 773 = some (CopyToT.expected 5 767 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound767_c : CopyToT.Bound exactSites 5 767 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row767_c0
  · exact row767_c1
  · exact row767_c2
  · exact row767_c3
  · exact row767_c4
  · exact row767_c5
  · exact row767_c6
theorem block767 : AXMacro.Realizes exactSites .copyH 767 774 :=
  AXMacro.copyH_realizes bound767_c
private theorem row774_u0 : resolveAt exactSites 774 = some (UnpairPartial.expected 774 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_u1 : resolveAt exactSites 775 = some (UnpairPartial.expected 774 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_u2 : resolveAt exactSites 776 = some (UnpairPartial.expected 774 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_u3 : resolveAt exactSites 777 = some (UnpairPartial.expected 774 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_u4 : resolveAt exactSites 778 = some (UnpairPartial.expected 774 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_u5 : resolveAt exactSites 779 = some (UnpairPartial.expected 774 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_u6 : resolveAt exactSites 780 = some (UnpairPartial.expected 774 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_u7 : resolveAt exactSites 781 = some (UnpairPartial.expected 774 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_u8 : resolveAt exactSites 782 = some (UnpairPartial.expected 774 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_u9 : resolveAt exactSites 783 = some (UnpairPartial.expected 774 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_u10 : resolveAt exactSites 784 = some (UnpairPartial.expected 774 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound774_u : UnpairPartial.Bound exactSites 774 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row774_u0
  · exact row774_u1
  · exact row774_u2
  · exact row774_u3
  · exact row774_u4
  · exact row774_u5
  · exact row774_u6
  · exact row774_u7
  · exact row774_u8
  · exact row774_u9
  · exact row774_u10
private theorem row774_q0 : resolveAt exactSites 785 = some (AXPair.relocate 754 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_q1 : resolveAt exactSites 786 = some (AXPair.relocate 754 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_q2 : resolveAt exactSites 787 = some (AXPair.relocate 754 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_q3 : resolveAt exactSites 788 = some (AXPair.relocate 754 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_q4 : resolveAt exactSites 789 = some (AXPair.relocate 754 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_q5 : resolveAt exactSites 790 = some (AXPair.relocate 754 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_q6 : resolveAt exactSites 791 = some (AXPair.relocate 754 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_q7 : resolveAt exactSites 792 = some (AXPair.relocate 754 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_q8 : resolveAt exactSites 793 = some (AXPair.relocate 754 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_q9 : resolveAt exactSites 794 = some (AXPair.relocate 754 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound774_q : AXPair.Bound exactSites 754 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row774_q0
  · exact row774_q1
  · exact row774_q2
  · exact row774_q3
  · exact row774_q4
  · exact row774_q5
  · exact row774_q6
  · exact row774_q7
  · exact row774_q8
  · exact row774_q9
private theorem row774_m0 : resolveAt exactSites 795 = some (AXTimes4.expected 795 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_m1 : resolveAt exactSites 796 = some (AXTimes4.expected 795 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_m2 : resolveAt exactSites 797 = some (AXTimes4.expected 795 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_m3 : resolveAt exactSites 798 = some (AXTimes4.expected 795 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_m4 : resolveAt exactSites 799 = some (AXTimes4.expected 795 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row774_m5 : resolveAt exactSites 800 = some (AXTimes4.expected 795 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound774_m : AXTimes4.Bound exactSites 795 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row774_m0
  · exact row774_m1
  · exact row774_m2
  · exact row774_m3
  · exact row774_m4
  · exact row774_m5
theorem block774 : AXMacro.Realizes exactSites .cons 774 801 :=
  AXMacro.cons_realizes bound774_u bound774_q bound774_m
private theorem row801_i0 : resolveAt exactSites 801 = some (Instruction.inc 1 (some 802)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block801 : AXMacro.Realizes exactSites .incT 801 802 :=
  AXMacro.inc_realizes row801_i0
private theorem row802_i0 : resolveAt exactSites 802 = some (Instruction.inc 1 (some 803)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block802 : AXMacro.Realizes exactSites .incT 802 803 :=
  AXMacro.inc_realizes row802_i0
private theorem row803_i0 : resolveAt exactSites 803 = some (Instruction.inc 1 (some 804)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block803 : AXMacro.Realizes exactSites .incT 803 804 :=
  AXMacro.inc_realizes row803_i0
private theorem row804_u0 : resolveAt exactSites 804 = some (UnpairPartial.expected 804 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_u1 : resolveAt exactSites 805 = some (UnpairPartial.expected 804 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_u2 : resolveAt exactSites 806 = some (UnpairPartial.expected 804 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_u3 : resolveAt exactSites 807 = some (UnpairPartial.expected 804 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_u4 : resolveAt exactSites 808 = some (UnpairPartial.expected 804 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_u5 : resolveAt exactSites 809 = some (UnpairPartial.expected 804 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_u6 : resolveAt exactSites 810 = some (UnpairPartial.expected 804 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_u7 : resolveAt exactSites 811 = some (UnpairPartial.expected 804 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_u8 : resolveAt exactSites 812 = some (UnpairPartial.expected 804 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_u9 : resolveAt exactSites 813 = some (UnpairPartial.expected 804 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_u10 : resolveAt exactSites 814 = some (UnpairPartial.expected 804 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound804_u : UnpairPartial.Bound exactSites 804 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row804_u0
  · exact row804_u1
  · exact row804_u2
  · exact row804_u3
  · exact row804_u4
  · exact row804_u5
  · exact row804_u6
  · exact row804_u7
  · exact row804_u8
  · exact row804_u9
  · exact row804_u10
private theorem row804_q0 : resolveAt exactSites 815 = some (AXPair.relocate 784 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_q1 : resolveAt exactSites 816 = some (AXPair.relocate 784 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_q2 : resolveAt exactSites 817 = some (AXPair.relocate 784 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_q3 : resolveAt exactSites 818 = some (AXPair.relocate 784 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_q4 : resolveAt exactSites 819 = some (AXPair.relocate 784 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_q5 : resolveAt exactSites 820 = some (AXPair.relocate 784 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_q6 : resolveAt exactSites 821 = some (AXPair.relocate 784 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_q7 : resolveAt exactSites 822 = some (AXPair.relocate 784 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_q8 : resolveAt exactSites 823 = some (AXPair.relocate 784 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_q9 : resolveAt exactSites 824 = some (AXPair.relocate 784 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound804_q : AXPair.Bound exactSites 784 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row804_q0
  · exact row804_q1
  · exact row804_q2
  · exact row804_q3
  · exact row804_q4
  · exact row804_q5
  · exact row804_q6
  · exact row804_q7
  · exact row804_q8
  · exact row804_q9
private theorem row804_m0 : resolveAt exactSites 825 = some (AXTimes4.expected 825 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_m1 : resolveAt exactSites 826 = some (AXTimes4.expected 825 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_m2 : resolveAt exactSites 827 = some (AXTimes4.expected 825 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_m3 : resolveAt exactSites 828 = some (AXTimes4.expected 825 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_m4 : resolveAt exactSites 829 = some (AXTimes4.expected 825 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row804_m5 : resolveAt exactSites 830 = some (AXTimes4.expected 825 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound804_m : AXTimes4.Bound exactSites 825 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row804_m0
  · exact row804_m1
  · exact row804_m2
  · exact row804_m3
  · exact row804_m4
  · exact row804_m5
theorem block804 : AXMacro.Realizes exactSites .cons 804 831 :=
  AXMacro.cons_realizes bound804_u bound804_q bound804_m
def code004 : List AXMacro.Op := [.copyH,.cons,.incT,.push,.copyD,.push,.copyH,.cons,.incT,.incT,.incT,.cons]
theorem plan004 : AXMacro.Plan exactSites 687 831 code004 :=
  AXMacro.Plan.cons block687 ( AXMacro.Plan.cons block694 ( AXMacro.Plan.cons block721 ( AXMacro.Plan.cons block722 ( AXMacro.Plan.cons block741 ( AXMacro.Plan.cons block748 ( AXMacro.Plan.cons block767 ( AXMacro.Plan.cons block774 ( AXMacro.Plan.cons block801 ( AXMacro.Plan.cons block802 ( AXMacro.Plan.cons block803 ( AXMacro.Plan.cons block804 ( AXMacro.Plan.nil 831))))))))))))
#print axioms plan004
end M6.Source.AXAll

