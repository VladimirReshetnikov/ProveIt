module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row831_i0 : resolveAt exactSites 831 = some (Instruction.inc 1 (some 832)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block831 : AXMacro.Realizes exactSites .incT 831 832 :=
  AXMacro.inc_realizes row831_i0
private theorem row832_i0 : resolveAt exactSites 832 = some (Instruction.inc 1 (some 833)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block832 : AXMacro.Realizes exactSites .incT 832 833 :=
  AXMacro.inc_realizes row832_i0
private theorem row833_u0 : resolveAt exactSites 833 = some (UnpairPartial.expected 833 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_u1 : resolveAt exactSites 834 = some (UnpairPartial.expected 833 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_u2 : resolveAt exactSites 835 = some (UnpairPartial.expected 833 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_u3 : resolveAt exactSites 836 = some (UnpairPartial.expected 833 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_u4 : resolveAt exactSites 837 = some (UnpairPartial.expected 833 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_u5 : resolveAt exactSites 838 = some (UnpairPartial.expected 833 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_u6 : resolveAt exactSites 839 = some (UnpairPartial.expected 833 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_u7 : resolveAt exactSites 840 = some (UnpairPartial.expected 833 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_u8 : resolveAt exactSites 841 = some (UnpairPartial.expected 833 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_u9 : resolveAt exactSites 842 = some (UnpairPartial.expected 833 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_u10 : resolveAt exactSites 843 = some (UnpairPartial.expected 833 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound833_u : UnpairPartial.Bound exactSites 833 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row833_u0
  · exact row833_u1
  · exact row833_u2
  · exact row833_u3
  · exact row833_u4
  · exact row833_u5
  · exact row833_u6
  · exact row833_u7
  · exact row833_u8
  · exact row833_u9
  · exact row833_u10
private theorem row833_q0 : resolveAt exactSites 844 = some (AXPair.relocate 813 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_q1 : resolveAt exactSites 845 = some (AXPair.relocate 813 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_q2 : resolveAt exactSites 846 = some (AXPair.relocate 813 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_q3 : resolveAt exactSites 847 = some (AXPair.relocate 813 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_q4 : resolveAt exactSites 848 = some (AXPair.relocate 813 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_q5 : resolveAt exactSites 849 = some (AXPair.relocate 813 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_q6 : resolveAt exactSites 850 = some (AXPair.relocate 813 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_q7 : resolveAt exactSites 851 = some (AXPair.relocate 813 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_q8 : resolveAt exactSites 852 = some (AXPair.relocate 813 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_q9 : resolveAt exactSites 853 = some (AXPair.relocate 813 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound833_q : AXPair.Bound exactSites 813 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row833_q0
  · exact row833_q1
  · exact row833_q2
  · exact row833_q3
  · exact row833_q4
  · exact row833_q5
  · exact row833_q6
  · exact row833_q7
  · exact row833_q8
  · exact row833_q9
private theorem row833_m0 : resolveAt exactSites 854 = some (AXTimes4.expected 854 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_m1 : resolveAt exactSites 855 = some (AXTimes4.expected 854 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_m2 : resolveAt exactSites 856 = some (AXTimes4.expected 854 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_m3 : resolveAt exactSites 857 = some (AXTimes4.expected 854 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_m4 : resolveAt exactSites 858 = some (AXTimes4.expected 854 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row833_m5 : resolveAt exactSites 859 = some (AXTimes4.expected 854 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound833_m : AXTimes4.Bound exactSites 854 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row833_m0
  · exact row833_m1
  · exact row833_m2
  · exact row833_m3
  · exact row833_m4
  · exact row833_m5
theorem block833 : AXMacro.Realizes exactSites .cons 833 860 :=
  AXMacro.cons_realizes bound833_u bound833_q bound833_m
private theorem row860_u0 : resolveAt exactSites 860 = some (UnpairPartial.expected 860 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_u1 : resolveAt exactSites 861 = some (UnpairPartial.expected 860 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_u2 : resolveAt exactSites 862 = some (UnpairPartial.expected 860 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_u3 : resolveAt exactSites 863 = some (UnpairPartial.expected 860 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_u4 : resolveAt exactSites 864 = some (UnpairPartial.expected 860 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_u5 : resolveAt exactSites 865 = some (UnpairPartial.expected 860 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_u6 : resolveAt exactSites 866 = some (UnpairPartial.expected 860 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_u7 : resolveAt exactSites 867 = some (UnpairPartial.expected 860 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_u8 : resolveAt exactSites 868 = some (UnpairPartial.expected 860 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_u9 : resolveAt exactSites 869 = some (UnpairPartial.expected 860 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_u10 : resolveAt exactSites 870 = some (UnpairPartial.expected 860 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound860_u : UnpairPartial.Bound exactSites 860 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row860_u0
  · exact row860_u1
  · exact row860_u2
  · exact row860_u3
  · exact row860_u4
  · exact row860_u5
  · exact row860_u6
  · exact row860_u7
  · exact row860_u8
  · exact row860_u9
  · exact row860_u10
private theorem row860_q0 : resolveAt exactSites 871 = some (AXPair.relocate 840 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_q1 : resolveAt exactSites 872 = some (AXPair.relocate 840 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_q2 : resolveAt exactSites 873 = some (AXPair.relocate 840 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_q3 : resolveAt exactSites 874 = some (AXPair.relocate 840 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_q4 : resolveAt exactSites 875 = some (AXPair.relocate 840 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_q5 : resolveAt exactSites 876 = some (AXPair.relocate 840 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_q6 : resolveAt exactSites 877 = some (AXPair.relocate 840 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_q7 : resolveAt exactSites 878 = some (AXPair.relocate 840 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_q8 : resolveAt exactSites 879 = some (AXPair.relocate 840 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_q9 : resolveAt exactSites 880 = some (AXPair.relocate 840 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound860_q : AXPair.Bound exactSites 840 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row860_q0
  · exact row860_q1
  · exact row860_q2
  · exact row860_q3
  · exact row860_q4
  · exact row860_q5
  · exact row860_q6
  · exact row860_q7
  · exact row860_q8
  · exact row860_q9
private theorem row860_m0 : resolveAt exactSites 881 = some (AXTimes4.expected 881 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_m1 : resolveAt exactSites 882 = some (AXTimes4.expected 881 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_m2 : resolveAt exactSites 883 = some (AXTimes4.expected 881 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_m3 : resolveAt exactSites 884 = some (AXTimes4.expected 881 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_m4 : resolveAt exactSites 885 = some (AXTimes4.expected 881 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row860_m5 : resolveAt exactSites 886 = some (AXTimes4.expected 881 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound860_m : AXTimes4.Bound exactSites 881 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row860_m0
  · exact row860_m1
  · exact row860_m2
  · exact row860_m3
  · exact row860_m4
  · exact row860_m5
theorem block860 : AXMacro.Realizes exactSites .cons 860 887 :=
  AXMacro.cons_realizes bound860_u bound860_q bound860_m
private theorem row887_p0 : resolveAt exactSites 887 = some (AXPushParam.relocate 862 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p1 : resolveAt exactSites 888 = some (AXPushParam.relocate 862 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p2 : resolveAt exactSites 889 = some (AXPushParam.relocate 862 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p3 : resolveAt exactSites 890 = some (AXPushParam.relocate 862 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p4 : resolveAt exactSites 891 = some (AXPushParam.relocate 862 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p5 : resolveAt exactSites 892 = some (AXPushParam.relocate 862 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p6 : resolveAt exactSites 893 = some (AXPushParam.relocate 862 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p7 : resolveAt exactSites 894 = some (AXPushParam.relocate 862 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p8 : resolveAt exactSites 895 = some (AXPushParam.relocate 862 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p9 : resolveAt exactSites 896 = some (AXPushParam.relocate 862 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p10 : resolveAt exactSites 897 = some (AXPushParam.relocate 862 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p11 : resolveAt exactSites 898 = some (AXPushParam.relocate 862 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p12 : resolveAt exactSites 899 = some (AXPushParam.relocate 862 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p13 : resolveAt exactSites 900 = some (AXPushParam.relocate 862 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p14 : resolveAt exactSites 901 = some (AXPushParam.relocate 862 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p15 : resolveAt exactSites 902 = some (AXPushParam.relocate 862 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p16 : resolveAt exactSites 903 = some (AXPushParam.relocate 862 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p17 : resolveAt exactSites 904 = some (AXPushParam.relocate 862 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row887_p18 : resolveAt exactSites 905 = some (AXPushParam.relocate 862 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound887_p : AXPushParam.Bound exactSites 862 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row887_p0
  · exact row887_p1
  · exact row887_p2
  · exact row887_p3
  · exact row887_p4
  · exact row887_p5
  · exact row887_p6
  · exact row887_p7
  · exact row887_p8
  · exact row887_p9
  · exact row887_p10
  · exact row887_p11
  · exact row887_p12
  · exact row887_p13
  · exact row887_p14
  · exact row887_p15
  · exact row887_p16
  · exact row887_p17
  · exact row887_p18
theorem block887 : AXMacro.Realizes exactSites .push 887 906 :=
  AXMacro.push_realizes bound887_p
private theorem row906_c0 : resolveAt exactSites 906 = some (CopyToT.expected 4 906 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row906_c1 : resolveAt exactSites 907 = some (CopyToT.expected 4 906 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row906_c2 : resolveAt exactSites 908 = some (CopyToT.expected 4 906 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row906_c3 : resolveAt exactSites 909 = some (CopyToT.expected 4 906 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row906_c4 : resolveAt exactSites 910 = some (CopyToT.expected 4 906 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row906_c5 : resolveAt exactSites 911 = some (CopyToT.expected 4 906 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row906_c6 : resolveAt exactSites 912 = some (CopyToT.expected 4 906 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound906_c : CopyToT.Bound exactSites 4 906 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row906_c0
  · exact row906_c1
  · exact row906_c2
  · exact row906_c3
  · exact row906_c4
  · exact row906_c5
  · exact row906_c6
theorem block906 : AXMacro.Realizes exactSites .copyD 906 913 :=
  AXMacro.copyD_realizes bound906_c
private theorem row913_p0 : resolveAt exactSites 913 = some (AXPushParam.relocate 888 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p1 : resolveAt exactSites 914 = some (AXPushParam.relocate 888 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p2 : resolveAt exactSites 915 = some (AXPushParam.relocate 888 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p3 : resolveAt exactSites 916 = some (AXPushParam.relocate 888 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p4 : resolveAt exactSites 917 = some (AXPushParam.relocate 888 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p5 : resolveAt exactSites 918 = some (AXPushParam.relocate 888 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p6 : resolveAt exactSites 919 = some (AXPushParam.relocate 888 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p7 : resolveAt exactSites 920 = some (AXPushParam.relocate 888 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p8 : resolveAt exactSites 921 = some (AXPushParam.relocate 888 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p9 : resolveAt exactSites 922 = some (AXPushParam.relocate 888 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p10 : resolveAt exactSites 923 = some (AXPushParam.relocate 888 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p11 : resolveAt exactSites 924 = some (AXPushParam.relocate 888 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p12 : resolveAt exactSites 925 = some (AXPushParam.relocate 888 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p13 : resolveAt exactSites 926 = some (AXPushParam.relocate 888 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p14 : resolveAt exactSites 927 = some (AXPushParam.relocate 888 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p15 : resolveAt exactSites 928 = some (AXPushParam.relocate 888 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p16 : resolveAt exactSites 929 = some (AXPushParam.relocate 888 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p17 : resolveAt exactSites 930 = some (AXPushParam.relocate 888 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row913_p18 : resolveAt exactSites 931 = some (AXPushParam.relocate 888 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound913_p : AXPushParam.Bound exactSites 888 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row913_p0
  · exact row913_p1
  · exact row913_p2
  · exact row913_p3
  · exact row913_p4
  · exact row913_p5
  · exact row913_p6
  · exact row913_p7
  · exact row913_p8
  · exact row913_p9
  · exact row913_p10
  · exact row913_p11
  · exact row913_p12
  · exact row913_p13
  · exact row913_p14
  · exact row913_p15
  · exact row913_p16
  · exact row913_p17
  · exact row913_p18
theorem block913 : AXMacro.Realizes exactSites .push 913 932 :=
  AXMacro.push_realizes bound913_p
private theorem row932_c0 : resolveAt exactSites 932 = some (CopyToT.expected 4 932 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row932_c1 : resolveAt exactSites 933 = some (CopyToT.expected 4 932 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row932_c2 : resolveAt exactSites 934 = some (CopyToT.expected 4 932 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row932_c3 : resolveAt exactSites 935 = some (CopyToT.expected 4 932 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row932_c4 : resolveAt exactSites 936 = some (CopyToT.expected 4 932 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row932_c5 : resolveAt exactSites 937 = some (CopyToT.expected 4 932 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row932_c6 : resolveAt exactSites 938 = some (CopyToT.expected 4 932 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound932_c : CopyToT.Bound exactSites 4 932 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row932_c0
  · exact row932_c1
  · exact row932_c2
  · exact row932_c3
  · exact row932_c4
  · exact row932_c5
  · exact row932_c6
theorem block932 : AXMacro.Realizes exactSites .copyD 932 939 :=
  AXMacro.copyD_realizes bound932_c
private theorem row939_p0 : resolveAt exactSites 939 = some (AXPushParam.relocate 914 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p1 : resolveAt exactSites 940 = some (AXPushParam.relocate 914 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p2 : resolveAt exactSites 941 = some (AXPushParam.relocate 914 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p3 : resolveAt exactSites 942 = some (AXPushParam.relocate 914 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p4 : resolveAt exactSites 943 = some (AXPushParam.relocate 914 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p5 : resolveAt exactSites 944 = some (AXPushParam.relocate 914 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p6 : resolveAt exactSites 945 = some (AXPushParam.relocate 914 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p7 : resolveAt exactSites 946 = some (AXPushParam.relocate 914 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p8 : resolveAt exactSites 947 = some (AXPushParam.relocate 914 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p9 : resolveAt exactSites 948 = some (AXPushParam.relocate 914 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p10 : resolveAt exactSites 949 = some (AXPushParam.relocate 914 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p11 : resolveAt exactSites 950 = some (AXPushParam.relocate 914 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p12 : resolveAt exactSites 951 = some (AXPushParam.relocate 914 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p13 : resolveAt exactSites 952 = some (AXPushParam.relocate 914 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p14 : resolveAt exactSites 953 = some (AXPushParam.relocate 914 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p15 : resolveAt exactSites 954 = some (AXPushParam.relocate 914 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p16 : resolveAt exactSites 955 = some (AXPushParam.relocate 914 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p17 : resolveAt exactSites 956 = some (AXPushParam.relocate 914 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row939_p18 : resolveAt exactSites 957 = some (AXPushParam.relocate 914 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound939_p : AXPushParam.Bound exactSites 914 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row939_p0
  · exact row939_p1
  · exact row939_p2
  · exact row939_p3
  · exact row939_p4
  · exact row939_p5
  · exact row939_p6
  · exact row939_p7
  · exact row939_p8
  · exact row939_p9
  · exact row939_p10
  · exact row939_p11
  · exact row939_p12
  · exact row939_p13
  · exact row939_p14
  · exact row939_p15
  · exact row939_p16
  · exact row939_p17
  · exact row939_p18
theorem block939 : AXMacro.Realizes exactSites .push 939 958 :=
  AXMacro.push_realizes bound939_p
private theorem row958_c0 : resolveAt exactSites 958 = some (CopyToT.expected 5 958 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row958_c1 : resolveAt exactSites 959 = some (CopyToT.expected 5 958 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row958_c2 : resolveAt exactSites 960 = some (CopyToT.expected 5 958 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row958_c3 : resolveAt exactSites 961 = some (CopyToT.expected 5 958 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row958_c4 : resolveAt exactSites 962 = some (CopyToT.expected 5 958 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row958_c5 : resolveAt exactSites 963 = some (CopyToT.expected 5 958 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row958_c6 : resolveAt exactSites 964 = some (CopyToT.expected 5 958 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound958_c : CopyToT.Bound exactSites 5 958 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row958_c0
  · exact row958_c1
  · exact row958_c2
  · exact row958_c3
  · exact row958_c4
  · exact row958_c5
  · exact row958_c6
theorem block958 : AXMacro.Realizes exactSites .copyH 958 965 :=
  AXMacro.copyH_realizes bound958_c
private theorem row965_u0 : resolveAt exactSites 965 = some (UnpairPartial.expected 965 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_u1 : resolveAt exactSites 966 = some (UnpairPartial.expected 965 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_u2 : resolveAt exactSites 967 = some (UnpairPartial.expected 965 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_u3 : resolveAt exactSites 968 = some (UnpairPartial.expected 965 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_u4 : resolveAt exactSites 969 = some (UnpairPartial.expected 965 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_u5 : resolveAt exactSites 970 = some (UnpairPartial.expected 965 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_u6 : resolveAt exactSites 971 = some (UnpairPartial.expected 965 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_u7 : resolveAt exactSites 972 = some (UnpairPartial.expected 965 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_u8 : resolveAt exactSites 973 = some (UnpairPartial.expected 965 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_u9 : resolveAt exactSites 974 = some (UnpairPartial.expected 965 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_u10 : resolveAt exactSites 975 = some (UnpairPartial.expected 965 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound965_u : UnpairPartial.Bound exactSites 965 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row965_u0
  · exact row965_u1
  · exact row965_u2
  · exact row965_u3
  · exact row965_u4
  · exact row965_u5
  · exact row965_u6
  · exact row965_u7
  · exact row965_u8
  · exact row965_u9
  · exact row965_u10
private theorem row965_q0 : resolveAt exactSites 976 = some (AXPair.relocate 945 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_q1 : resolveAt exactSites 977 = some (AXPair.relocate 945 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_q2 : resolveAt exactSites 978 = some (AXPair.relocate 945 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_q3 : resolveAt exactSites 979 = some (AXPair.relocate 945 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_q4 : resolveAt exactSites 980 = some (AXPair.relocate 945 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_q5 : resolveAt exactSites 981 = some (AXPair.relocate 945 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_q6 : resolveAt exactSites 982 = some (AXPair.relocate 945 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_q7 : resolveAt exactSites 983 = some (AXPair.relocate 945 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_q8 : resolveAt exactSites 984 = some (AXPair.relocate 945 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_q9 : resolveAt exactSites 985 = some (AXPair.relocate 945 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound965_q : AXPair.Bound exactSites 945 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row965_q0
  · exact row965_q1
  · exact row965_q2
  · exact row965_q3
  · exact row965_q4
  · exact row965_q5
  · exact row965_q6
  · exact row965_q7
  · exact row965_q8
  · exact row965_q9
private theorem row965_m0 : resolveAt exactSites 986 = some (AXTimes4.expected 986 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_m1 : resolveAt exactSites 987 = some (AXTimes4.expected 986 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_m2 : resolveAt exactSites 988 = some (AXTimes4.expected 986 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_m3 : resolveAt exactSites 989 = some (AXTimes4.expected 986 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_m4 : resolveAt exactSites 990 = some (AXTimes4.expected 986 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row965_m5 : resolveAt exactSites 991 = some (AXTimes4.expected 986 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound965_m : AXTimes4.Bound exactSites 986 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row965_m0
  · exact row965_m1
  · exact row965_m2
  · exact row965_m3
  · exact row965_m4
  · exact row965_m5
theorem block965 : AXMacro.Realizes exactSites .cons 965 992 :=
  AXMacro.cons_realizes bound965_u bound965_q bound965_m
private theorem row992_i0 : resolveAt exactSites 992 = some (Instruction.inc 1 (some 993)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block992 : AXMacro.Realizes exactSites .incT 992 993 :=
  AXMacro.inc_realizes row992_i0
def code005 : List AXMacro.Op := [.incT,.incT,.cons,.cons,.push,.copyD,.push,.copyD,.push,.copyH,.cons,.incT]
theorem plan005 : AXMacro.Plan exactSites 831 993 code005 :=
  AXMacro.Plan.cons block831 ( AXMacro.Plan.cons block832 ( AXMacro.Plan.cons block833 ( AXMacro.Plan.cons block860 ( AXMacro.Plan.cons block887 ( AXMacro.Plan.cons block906 ( AXMacro.Plan.cons block913 ( AXMacro.Plan.cons block932 ( AXMacro.Plan.cons block939 ( AXMacro.Plan.cons block958 ( AXMacro.Plan.cons block965 ( AXMacro.Plan.cons block992 ( AXMacro.Plan.nil 993))))))))))))
#print axioms plan005
end M6.Source.AXAll

