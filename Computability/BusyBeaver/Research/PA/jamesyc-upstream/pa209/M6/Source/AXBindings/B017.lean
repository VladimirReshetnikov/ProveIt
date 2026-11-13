module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row2721_i0 : resolveAt exactSites 2721 = some (Instruction.inc 1 (some 2722)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block2721 : AXMacro.Realizes exactSites .incT 2721 2722 :=
  AXMacro.inc_realizes row2721_i0
private theorem row2722_p0 : resolveAt exactSites 2722 = some (AXPushParam.relocate 2697 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p1 : resolveAt exactSites 2723 = some (AXPushParam.relocate 2697 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p2 : resolveAt exactSites 2724 = some (AXPushParam.relocate 2697 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p3 : resolveAt exactSites 2725 = some (AXPushParam.relocate 2697 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p4 : resolveAt exactSites 2726 = some (AXPushParam.relocate 2697 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p5 : resolveAt exactSites 2727 = some (AXPushParam.relocate 2697 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p6 : resolveAt exactSites 2728 = some (AXPushParam.relocate 2697 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p7 : resolveAt exactSites 2729 = some (AXPushParam.relocate 2697 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p8 : resolveAt exactSites 2730 = some (AXPushParam.relocate 2697 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p9 : resolveAt exactSites 2731 = some (AXPushParam.relocate 2697 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p10 : resolveAt exactSites 2732 = some (AXPushParam.relocate 2697 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p11 : resolveAt exactSites 2733 = some (AXPushParam.relocate 2697 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p12 : resolveAt exactSites 2734 = some (AXPushParam.relocate 2697 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p13 : resolveAt exactSites 2735 = some (AXPushParam.relocate 2697 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p14 : resolveAt exactSites 2736 = some (AXPushParam.relocate 2697 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p15 : resolveAt exactSites 2737 = some (AXPushParam.relocate 2697 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p16 : resolveAt exactSites 2738 = some (AXPushParam.relocate 2697 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p17 : resolveAt exactSites 2739 = some (AXPushParam.relocate 2697 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2722_p18 : resolveAt exactSites 2740 = some (AXPushParam.relocate 2697 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2722_p : AXPushParam.Bound exactSites 2697 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2722_p0
  · exact row2722_p1
  · exact row2722_p2
  · exact row2722_p3
  · exact row2722_p4
  · exact row2722_p5
  · exact row2722_p6
  · exact row2722_p7
  · exact row2722_p8
  · exact row2722_p9
  · exact row2722_p10
  · exact row2722_p11
  · exact row2722_p12
  · exact row2722_p13
  · exact row2722_p14
  · exact row2722_p15
  · exact row2722_p16
  · exact row2722_p17
  · exact row2722_p18
theorem block2722 : AXMacro.Realizes exactSites .push 2722 2741 :=
  AXMacro.push_realizes bound2722_p
private theorem row2741_c0 : resolveAt exactSites 2741 = some (CopyToT.expected 3 2741 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2741_c1 : resolveAt exactSites 2742 = some (CopyToT.expected 3 2741 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2741_c2 : resolveAt exactSites 2743 = some (CopyToT.expected 3 2741 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2741_c3 : resolveAt exactSites 2744 = some (CopyToT.expected 3 2741 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2741_c4 : resolveAt exactSites 2745 = some (CopyToT.expected 3 2741 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2741_c5 : resolveAt exactSites 2746 = some (CopyToT.expected 3 2741 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2741_c6 : resolveAt exactSites 2747 = some (CopyToT.expected 3 2741 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2741_c : CopyToT.Bound exactSites 3 2741 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2741_c0
  · exact row2741_c1
  · exact row2741_c2
  · exact row2741_c3
  · exact row2741_c4
  · exact row2741_c5
  · exact row2741_c6
theorem block2741 : AXMacro.Realizes exactSites .copyA 2741 2748 :=
  AXMacro.copyA_realizes bound2741_c
private theorem row2748_p0 : resolveAt exactSites 2748 = some (AXPushParam.relocate 2723 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p1 : resolveAt exactSites 2749 = some (AXPushParam.relocate 2723 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p2 : resolveAt exactSites 2750 = some (AXPushParam.relocate 2723 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p3 : resolveAt exactSites 2751 = some (AXPushParam.relocate 2723 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p4 : resolveAt exactSites 2752 = some (AXPushParam.relocate 2723 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p5 : resolveAt exactSites 2753 = some (AXPushParam.relocate 2723 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p6 : resolveAt exactSites 2754 = some (AXPushParam.relocate 2723 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p7 : resolveAt exactSites 2755 = some (AXPushParam.relocate 2723 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p8 : resolveAt exactSites 2756 = some (AXPushParam.relocate 2723 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p9 : resolveAt exactSites 2757 = some (AXPushParam.relocate 2723 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p10 : resolveAt exactSites 2758 = some (AXPushParam.relocate 2723 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p11 : resolveAt exactSites 2759 = some (AXPushParam.relocate 2723 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p12 : resolveAt exactSites 2760 = some (AXPushParam.relocate 2723 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p13 : resolveAt exactSites 2761 = some (AXPushParam.relocate 2723 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p14 : resolveAt exactSites 2762 = some (AXPushParam.relocate 2723 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p15 : resolveAt exactSites 2763 = some (AXPushParam.relocate 2723 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p16 : resolveAt exactSites 2764 = some (AXPushParam.relocate 2723 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p17 : resolveAt exactSites 2765 = some (AXPushParam.relocate 2723 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2748_p18 : resolveAt exactSites 2766 = some (AXPushParam.relocate 2723 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2748_p : AXPushParam.Bound exactSites 2723 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2748_p0
  · exact row2748_p1
  · exact row2748_p2
  · exact row2748_p3
  · exact row2748_p4
  · exact row2748_p5
  · exact row2748_p6
  · exact row2748_p7
  · exact row2748_p8
  · exact row2748_p9
  · exact row2748_p10
  · exact row2748_p11
  · exact row2748_p12
  · exact row2748_p13
  · exact row2748_p14
  · exact row2748_p15
  · exact row2748_p16
  · exact row2748_p17
  · exact row2748_p18
theorem block2748 : AXMacro.Realizes exactSites .push 2748 2767 :=
  AXMacro.push_realizes bound2748_p
private theorem row2767_c0 : resolveAt exactSites 2767 = some (CopyToT.expected 4 2767 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2767_c1 : resolveAt exactSites 2768 = some (CopyToT.expected 4 2767 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2767_c2 : resolveAt exactSites 2769 = some (CopyToT.expected 4 2767 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2767_c3 : resolveAt exactSites 2770 = some (CopyToT.expected 4 2767 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2767_c4 : resolveAt exactSites 2771 = some (CopyToT.expected 4 2767 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2767_c5 : resolveAt exactSites 2772 = some (CopyToT.expected 4 2767 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2767_c6 : resolveAt exactSites 2773 = some (CopyToT.expected 4 2767 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2767_c : CopyToT.Bound exactSites 4 2767 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2767_c0
  · exact row2767_c1
  · exact row2767_c2
  · exact row2767_c3
  · exact row2767_c4
  · exact row2767_c5
  · exact row2767_c6
theorem block2767 : AXMacro.Realizes exactSites .copyD 2767 2774 :=
  AXMacro.copyD_realizes bound2767_c
private theorem row2774_p0 : resolveAt exactSites 2774 = some (AXPushParam.relocate 2749 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p1 : resolveAt exactSites 2775 = some (AXPushParam.relocate 2749 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p2 : resolveAt exactSites 2776 = some (AXPushParam.relocate 2749 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p3 : resolveAt exactSites 2777 = some (AXPushParam.relocate 2749 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p4 : resolveAt exactSites 2778 = some (AXPushParam.relocate 2749 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p5 : resolveAt exactSites 2779 = some (AXPushParam.relocate 2749 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p6 : resolveAt exactSites 2780 = some (AXPushParam.relocate 2749 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p7 : resolveAt exactSites 2781 = some (AXPushParam.relocate 2749 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p8 : resolveAt exactSites 2782 = some (AXPushParam.relocate 2749 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p9 : resolveAt exactSites 2783 = some (AXPushParam.relocate 2749 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p10 : resolveAt exactSites 2784 = some (AXPushParam.relocate 2749 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p11 : resolveAt exactSites 2785 = some (AXPushParam.relocate 2749 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p12 : resolveAt exactSites 2786 = some (AXPushParam.relocate 2749 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p13 : resolveAt exactSites 2787 = some (AXPushParam.relocate 2749 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p14 : resolveAt exactSites 2788 = some (AXPushParam.relocate 2749 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p15 : resolveAt exactSites 2789 = some (AXPushParam.relocate 2749 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p16 : resolveAt exactSites 2790 = some (AXPushParam.relocate 2749 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p17 : resolveAt exactSites 2791 = some (AXPushParam.relocate 2749 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2774_p18 : resolveAt exactSites 2792 = some (AXPushParam.relocate 2749 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2774_p : AXPushParam.Bound exactSites 2749 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2774_p0
  · exact row2774_p1
  · exact row2774_p2
  · exact row2774_p3
  · exact row2774_p4
  · exact row2774_p5
  · exact row2774_p6
  · exact row2774_p7
  · exact row2774_p8
  · exact row2774_p9
  · exact row2774_p10
  · exact row2774_p11
  · exact row2774_p12
  · exact row2774_p13
  · exact row2774_p14
  · exact row2774_p15
  · exact row2774_p16
  · exact row2774_p17
  · exact row2774_p18
theorem block2774 : AXMacro.Realizes exactSites .push 2774 2793 :=
  AXMacro.push_realizes bound2774_p
private theorem row2793_c0 : resolveAt exactSites 2793 = some (CopyToT.expected 5 2793 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2793_c1 : resolveAt exactSites 2794 = some (CopyToT.expected 5 2793 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2793_c2 : resolveAt exactSites 2795 = some (CopyToT.expected 5 2793 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2793_c3 : resolveAt exactSites 2796 = some (CopyToT.expected 5 2793 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2793_c4 : resolveAt exactSites 2797 = some (CopyToT.expected 5 2793 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2793_c5 : resolveAt exactSites 2798 = some (CopyToT.expected 5 2793 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2793_c6 : resolveAt exactSites 2799 = some (CopyToT.expected 5 2793 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2793_c : CopyToT.Bound exactSites 5 2793 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2793_c0
  · exact row2793_c1
  · exact row2793_c2
  · exact row2793_c3
  · exact row2793_c4
  · exact row2793_c5
  · exact row2793_c6
theorem block2793 : AXMacro.Realizes exactSites .copyH 2793 2800 :=
  AXMacro.copyH_realizes bound2793_c
private theorem row2800_u0 : resolveAt exactSites 2800 = some (UnpairPartial.expected 2800 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_u1 : resolveAt exactSites 2801 = some (UnpairPartial.expected 2800 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_u2 : resolveAt exactSites 2802 = some (UnpairPartial.expected 2800 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_u3 : resolveAt exactSites 2803 = some (UnpairPartial.expected 2800 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_u4 : resolveAt exactSites 2804 = some (UnpairPartial.expected 2800 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_u5 : resolveAt exactSites 2805 = some (UnpairPartial.expected 2800 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_u6 : resolveAt exactSites 2806 = some (UnpairPartial.expected 2800 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_u7 : resolveAt exactSites 2807 = some (UnpairPartial.expected 2800 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_u8 : resolveAt exactSites 2808 = some (UnpairPartial.expected 2800 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_u9 : resolveAt exactSites 2809 = some (UnpairPartial.expected 2800 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_u10 : resolveAt exactSites 2810 = some (UnpairPartial.expected 2800 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2800_u : UnpairPartial.Bound exactSites 2800 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2800_u0
  · exact row2800_u1
  · exact row2800_u2
  · exact row2800_u3
  · exact row2800_u4
  · exact row2800_u5
  · exact row2800_u6
  · exact row2800_u7
  · exact row2800_u8
  · exact row2800_u9
  · exact row2800_u10
private theorem row2800_q0 : resolveAt exactSites 2811 = some (AXPair.relocate 2780 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_q1 : resolveAt exactSites 2812 = some (AXPair.relocate 2780 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_q2 : resolveAt exactSites 2813 = some (AXPair.relocate 2780 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_q3 : resolveAt exactSites 2814 = some (AXPair.relocate 2780 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_q4 : resolveAt exactSites 2815 = some (AXPair.relocate 2780 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_q5 : resolveAt exactSites 2816 = some (AXPair.relocate 2780 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_q6 : resolveAt exactSites 2817 = some (AXPair.relocate 2780 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_q7 : resolveAt exactSites 2818 = some (AXPair.relocate 2780 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_q8 : resolveAt exactSites 2819 = some (AXPair.relocate 2780 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_q9 : resolveAt exactSites 2820 = some (AXPair.relocate 2780 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2800_q : AXPair.Bound exactSites 2780 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2800_q0
  · exact row2800_q1
  · exact row2800_q2
  · exact row2800_q3
  · exact row2800_q4
  · exact row2800_q5
  · exact row2800_q6
  · exact row2800_q7
  · exact row2800_q8
  · exact row2800_q9
private theorem row2800_m0 : resolveAt exactSites 2821 = some (AXTimes4.expected 2821 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_m1 : resolveAt exactSites 2822 = some (AXTimes4.expected 2821 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_m2 : resolveAt exactSites 2823 = some (AXTimes4.expected 2821 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_m3 : resolveAt exactSites 2824 = some (AXTimes4.expected 2821 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_m4 : resolveAt exactSites 2825 = some (AXTimes4.expected 2821 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2800_m5 : resolveAt exactSites 2826 = some (AXTimes4.expected 2821 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2800_m : AXTimes4.Bound exactSites 2821 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2800_m0
  · exact row2800_m1
  · exact row2800_m2
  · exact row2800_m3
  · exact row2800_m4
  · exact row2800_m5
theorem block2800 : AXMacro.Realizes exactSites .cons 2800 2827 :=
  AXMacro.cons_realizes bound2800_u bound2800_q bound2800_m
private theorem row2827_i0 : resolveAt exactSites 2827 = some (Instruction.inc 1 (some 2828)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block2827 : AXMacro.Realizes exactSites .incT 2827 2828 :=
  AXMacro.inc_realizes row2827_i0
private theorem row2828_u0 : resolveAt exactSites 2828 = some (UnpairPartial.expected 2828 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_u1 : resolveAt exactSites 2829 = some (UnpairPartial.expected 2828 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_u2 : resolveAt exactSites 2830 = some (UnpairPartial.expected 2828 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_u3 : resolveAt exactSites 2831 = some (UnpairPartial.expected 2828 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_u4 : resolveAt exactSites 2832 = some (UnpairPartial.expected 2828 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_u5 : resolveAt exactSites 2833 = some (UnpairPartial.expected 2828 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_u6 : resolveAt exactSites 2834 = some (UnpairPartial.expected 2828 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_u7 : resolveAt exactSites 2835 = some (UnpairPartial.expected 2828 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_u8 : resolveAt exactSites 2836 = some (UnpairPartial.expected 2828 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_u9 : resolveAt exactSites 2837 = some (UnpairPartial.expected 2828 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_u10 : resolveAt exactSites 2838 = some (UnpairPartial.expected 2828 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2828_u : UnpairPartial.Bound exactSites 2828 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2828_u0
  · exact row2828_u1
  · exact row2828_u2
  · exact row2828_u3
  · exact row2828_u4
  · exact row2828_u5
  · exact row2828_u6
  · exact row2828_u7
  · exact row2828_u8
  · exact row2828_u9
  · exact row2828_u10
private theorem row2828_q0 : resolveAt exactSites 2839 = some (AXPair.relocate 2808 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_q1 : resolveAt exactSites 2840 = some (AXPair.relocate 2808 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_q2 : resolveAt exactSites 2841 = some (AXPair.relocate 2808 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_q3 : resolveAt exactSites 2842 = some (AXPair.relocate 2808 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_q4 : resolveAt exactSites 2843 = some (AXPair.relocate 2808 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_q5 : resolveAt exactSites 2844 = some (AXPair.relocate 2808 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_q6 : resolveAt exactSites 2845 = some (AXPair.relocate 2808 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_q7 : resolveAt exactSites 2846 = some (AXPair.relocate 2808 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_q8 : resolveAt exactSites 2847 = some (AXPair.relocate 2808 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_q9 : resolveAt exactSites 2848 = some (AXPair.relocate 2808 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2828_q : AXPair.Bound exactSites 2808 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2828_q0
  · exact row2828_q1
  · exact row2828_q2
  · exact row2828_q3
  · exact row2828_q4
  · exact row2828_q5
  · exact row2828_q6
  · exact row2828_q7
  · exact row2828_q8
  · exact row2828_q9
private theorem row2828_m0 : resolveAt exactSites 2849 = some (AXTimes4.expected 2849 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_m1 : resolveAt exactSites 2850 = some (AXTimes4.expected 2849 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_m2 : resolveAt exactSites 2851 = some (AXTimes4.expected 2849 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_m3 : resolveAt exactSites 2852 = some (AXTimes4.expected 2849 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_m4 : resolveAt exactSites 2853 = some (AXTimes4.expected 2849 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2828_m5 : resolveAt exactSites 2854 = some (AXTimes4.expected 2849 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2828_m : AXTimes4.Bound exactSites 2849 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2828_m0
  · exact row2828_m1
  · exact row2828_m2
  · exact row2828_m3
  · exact row2828_m4
  · exact row2828_m5
theorem block2828 : AXMacro.Realizes exactSites .cons 2828 2855 :=
  AXMacro.cons_realizes bound2828_u bound2828_q bound2828_m
private theorem row2855_i0 : resolveAt exactSites 2855 = some (Instruction.inc 1 (some 2856)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block2855 : AXMacro.Realizes exactSites .incT 2855 2856 :=
  AXMacro.inc_realizes row2855_i0
private theorem row2856_i0 : resolveAt exactSites 2856 = some (Instruction.inc 1 (some 2857)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block2856 : AXMacro.Realizes exactSites .incT 2856 2857 :=
  AXMacro.inc_realizes row2856_i0
def code017 : List AXMacro.Op := [.incT,.push,.copyA,.push,.copyD,.push,.copyH,.cons,.incT,.cons,.incT,.incT]
theorem plan017 : AXMacro.Plan exactSites 2721 2857 code017 :=
  AXMacro.Plan.cons block2721 ( AXMacro.Plan.cons block2722 ( AXMacro.Plan.cons block2741 ( AXMacro.Plan.cons block2748 ( AXMacro.Plan.cons block2767 ( AXMacro.Plan.cons block2774 ( AXMacro.Plan.cons block2793 ( AXMacro.Plan.cons block2800 ( AXMacro.Plan.cons block2827 ( AXMacro.Plan.cons block2828 ( AXMacro.Plan.cons block2855 ( AXMacro.Plan.cons block2856 ( AXMacro.Plan.nil 2857))))))))))))
#print axioms plan017
end M6.Source.AXAll

