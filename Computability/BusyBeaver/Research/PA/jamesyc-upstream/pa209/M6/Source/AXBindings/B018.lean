module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row2857_u0 : resolveAt exactSites 2857 = some (UnpairPartial.expected 2857 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_u1 : resolveAt exactSites 2858 = some (UnpairPartial.expected 2857 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_u2 : resolveAt exactSites 2859 = some (UnpairPartial.expected 2857 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_u3 : resolveAt exactSites 2860 = some (UnpairPartial.expected 2857 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_u4 : resolveAt exactSites 2861 = some (UnpairPartial.expected 2857 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_u5 : resolveAt exactSites 2862 = some (UnpairPartial.expected 2857 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_u6 : resolveAt exactSites 2863 = some (UnpairPartial.expected 2857 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_u7 : resolveAt exactSites 2864 = some (UnpairPartial.expected 2857 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_u8 : resolveAt exactSites 2865 = some (UnpairPartial.expected 2857 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_u9 : resolveAt exactSites 2866 = some (UnpairPartial.expected 2857 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_u10 : resolveAt exactSites 2867 = some (UnpairPartial.expected 2857 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2857_u : UnpairPartial.Bound exactSites 2857 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2857_u0
  · exact row2857_u1
  · exact row2857_u2
  · exact row2857_u3
  · exact row2857_u4
  · exact row2857_u5
  · exact row2857_u6
  · exact row2857_u7
  · exact row2857_u8
  · exact row2857_u9
  · exact row2857_u10
private theorem row2857_q0 : resolveAt exactSites 2868 = some (AXPair.relocate 2837 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_q1 : resolveAt exactSites 2869 = some (AXPair.relocate 2837 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_q2 : resolveAt exactSites 2870 = some (AXPair.relocate 2837 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_q3 : resolveAt exactSites 2871 = some (AXPair.relocate 2837 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_q4 : resolveAt exactSites 2872 = some (AXPair.relocate 2837 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_q5 : resolveAt exactSites 2873 = some (AXPair.relocate 2837 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_q6 : resolveAt exactSites 2874 = some (AXPair.relocate 2837 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_q7 : resolveAt exactSites 2875 = some (AXPair.relocate 2837 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_q8 : resolveAt exactSites 2876 = some (AXPair.relocate 2837 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_q9 : resolveAt exactSites 2877 = some (AXPair.relocate 2837 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2857_q : AXPair.Bound exactSites 2837 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2857_q0
  · exact row2857_q1
  · exact row2857_q2
  · exact row2857_q3
  · exact row2857_q4
  · exact row2857_q5
  · exact row2857_q6
  · exact row2857_q7
  · exact row2857_q8
  · exact row2857_q9
private theorem row2857_m0 : resolveAt exactSites 2878 = some (AXTimes4.expected 2878 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_m1 : resolveAt exactSites 2879 = some (AXTimes4.expected 2878 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_m2 : resolveAt exactSites 2880 = some (AXTimes4.expected 2878 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_m3 : resolveAt exactSites 2881 = some (AXTimes4.expected 2878 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_m4 : resolveAt exactSites 2882 = some (AXTimes4.expected 2878 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2857_m5 : resolveAt exactSites 2883 = some (AXTimes4.expected 2878 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2857_m : AXTimes4.Bound exactSites 2878 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2857_m0
  · exact row2857_m1
  · exact row2857_m2
  · exact row2857_m3
  · exact row2857_m4
  · exact row2857_m5
theorem block2857 : AXMacro.Realizes exactSites .cons 2857 2884 :=
  AXMacro.cons_realizes bound2857_u bound2857_q bound2857_m
private theorem row2884_p0 : resolveAt exactSites 2884 = some (AXPushParam.relocate 2859 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p1 : resolveAt exactSites 2885 = some (AXPushParam.relocate 2859 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p2 : resolveAt exactSites 2886 = some (AXPushParam.relocate 2859 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p3 : resolveAt exactSites 2887 = some (AXPushParam.relocate 2859 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p4 : resolveAt exactSites 2888 = some (AXPushParam.relocate 2859 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p5 : resolveAt exactSites 2889 = some (AXPushParam.relocate 2859 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p6 : resolveAt exactSites 2890 = some (AXPushParam.relocate 2859 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p7 : resolveAt exactSites 2891 = some (AXPushParam.relocate 2859 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p8 : resolveAt exactSites 2892 = some (AXPushParam.relocate 2859 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p9 : resolveAt exactSites 2893 = some (AXPushParam.relocate 2859 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p10 : resolveAt exactSites 2894 = some (AXPushParam.relocate 2859 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p11 : resolveAt exactSites 2895 = some (AXPushParam.relocate 2859 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p12 : resolveAt exactSites 2896 = some (AXPushParam.relocate 2859 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p13 : resolveAt exactSites 2897 = some (AXPushParam.relocate 2859 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p14 : resolveAt exactSites 2898 = some (AXPushParam.relocate 2859 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p15 : resolveAt exactSites 2899 = some (AXPushParam.relocate 2859 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p16 : resolveAt exactSites 2900 = some (AXPushParam.relocate 2859 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p17 : resolveAt exactSites 2901 = some (AXPushParam.relocate 2859 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2884_p18 : resolveAt exactSites 2902 = some (AXPushParam.relocate 2859 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2884_p : AXPushParam.Bound exactSites 2859 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2884_p0
  · exact row2884_p1
  · exact row2884_p2
  · exact row2884_p3
  · exact row2884_p4
  · exact row2884_p5
  · exact row2884_p6
  · exact row2884_p7
  · exact row2884_p8
  · exact row2884_p9
  · exact row2884_p10
  · exact row2884_p11
  · exact row2884_p12
  · exact row2884_p13
  · exact row2884_p14
  · exact row2884_p15
  · exact row2884_p16
  · exact row2884_p17
  · exact row2884_p18
theorem block2884 : AXMacro.Realizes exactSites .push 2884 2903 :=
  AXMacro.push_realizes bound2884_p
private theorem row2903_c0 : resolveAt exactSites 2903 = some (CopyToT.expected 3 2903 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2903_c1 : resolveAt exactSites 2904 = some (CopyToT.expected 3 2903 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2903_c2 : resolveAt exactSites 2905 = some (CopyToT.expected 3 2903 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2903_c3 : resolveAt exactSites 2906 = some (CopyToT.expected 3 2903 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2903_c4 : resolveAt exactSites 2907 = some (CopyToT.expected 3 2903 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2903_c5 : resolveAt exactSites 2908 = some (CopyToT.expected 3 2903 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2903_c6 : resolveAt exactSites 2909 = some (CopyToT.expected 3 2903 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2903_c : CopyToT.Bound exactSites 3 2903 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2903_c0
  · exact row2903_c1
  · exact row2903_c2
  · exact row2903_c3
  · exact row2903_c4
  · exact row2903_c5
  · exact row2903_c6
theorem block2903 : AXMacro.Realizes exactSites .copyA 2903 2910 :=
  AXMacro.copyA_realizes bound2903_c
private theorem row2910_p0 : resolveAt exactSites 2910 = some (AXPushParam.relocate 2885 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p1 : resolveAt exactSites 2911 = some (AXPushParam.relocate 2885 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p2 : resolveAt exactSites 2912 = some (AXPushParam.relocate 2885 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p3 : resolveAt exactSites 2913 = some (AXPushParam.relocate 2885 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p4 : resolveAt exactSites 2914 = some (AXPushParam.relocate 2885 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p5 : resolveAt exactSites 2915 = some (AXPushParam.relocate 2885 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p6 : resolveAt exactSites 2916 = some (AXPushParam.relocate 2885 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p7 : resolveAt exactSites 2917 = some (AXPushParam.relocate 2885 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p8 : resolveAt exactSites 2918 = some (AXPushParam.relocate 2885 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p9 : resolveAt exactSites 2919 = some (AXPushParam.relocate 2885 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p10 : resolveAt exactSites 2920 = some (AXPushParam.relocate 2885 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p11 : resolveAt exactSites 2921 = some (AXPushParam.relocate 2885 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p12 : resolveAt exactSites 2922 = some (AXPushParam.relocate 2885 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p13 : resolveAt exactSites 2923 = some (AXPushParam.relocate 2885 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p14 : resolveAt exactSites 2924 = some (AXPushParam.relocate 2885 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p15 : resolveAt exactSites 2925 = some (AXPushParam.relocate 2885 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p16 : resolveAt exactSites 2926 = some (AXPushParam.relocate 2885 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p17 : resolveAt exactSites 2927 = some (AXPushParam.relocate 2885 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2910_p18 : resolveAt exactSites 2928 = some (AXPushParam.relocate 2885 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2910_p : AXPushParam.Bound exactSites 2885 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2910_p0
  · exact row2910_p1
  · exact row2910_p2
  · exact row2910_p3
  · exact row2910_p4
  · exact row2910_p5
  · exact row2910_p6
  · exact row2910_p7
  · exact row2910_p8
  · exact row2910_p9
  · exact row2910_p10
  · exact row2910_p11
  · exact row2910_p12
  · exact row2910_p13
  · exact row2910_p14
  · exact row2910_p15
  · exact row2910_p16
  · exact row2910_p17
  · exact row2910_p18
theorem block2910 : AXMacro.Realizes exactSites .push 2910 2929 :=
  AXMacro.push_realizes bound2910_p
private theorem row2929_c0 : resolveAt exactSites 2929 = some (CopyToT.expected 5 2929 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2929_c1 : resolveAt exactSites 2930 = some (CopyToT.expected 5 2929 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2929_c2 : resolveAt exactSites 2931 = some (CopyToT.expected 5 2929 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2929_c3 : resolveAt exactSites 2932 = some (CopyToT.expected 5 2929 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2929_c4 : resolveAt exactSites 2933 = some (CopyToT.expected 5 2929 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2929_c5 : resolveAt exactSites 2934 = some (CopyToT.expected 5 2929 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2929_c6 : resolveAt exactSites 2935 = some (CopyToT.expected 5 2929 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2929_c : CopyToT.Bound exactSites 5 2929 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2929_c0
  · exact row2929_c1
  · exact row2929_c2
  · exact row2929_c3
  · exact row2929_c4
  · exact row2929_c5
  · exact row2929_c6
theorem block2929 : AXMacro.Realizes exactSites .copyH 2929 2936 :=
  AXMacro.copyH_realizes bound2929_c
private theorem row2936_p0 : resolveAt exactSites 2936 = some (AXPushParam.relocate 2911 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p1 : resolveAt exactSites 2937 = some (AXPushParam.relocate 2911 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p2 : resolveAt exactSites 2938 = some (AXPushParam.relocate 2911 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p3 : resolveAt exactSites 2939 = some (AXPushParam.relocate 2911 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p4 : resolveAt exactSites 2940 = some (AXPushParam.relocate 2911 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p5 : resolveAt exactSites 2941 = some (AXPushParam.relocate 2911 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p6 : resolveAt exactSites 2942 = some (AXPushParam.relocate 2911 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p7 : resolveAt exactSites 2943 = some (AXPushParam.relocate 2911 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p8 : resolveAt exactSites 2944 = some (AXPushParam.relocate 2911 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p9 : resolveAt exactSites 2945 = some (AXPushParam.relocate 2911 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p10 : resolveAt exactSites 2946 = some (AXPushParam.relocate 2911 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p11 : resolveAt exactSites 2947 = some (AXPushParam.relocate 2911 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p12 : resolveAt exactSites 2948 = some (AXPushParam.relocate 2911 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p13 : resolveAt exactSites 2949 = some (AXPushParam.relocate 2911 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p14 : resolveAt exactSites 2950 = some (AXPushParam.relocate 2911 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p15 : resolveAt exactSites 2951 = some (AXPushParam.relocate 2911 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p16 : resolveAt exactSites 2952 = some (AXPushParam.relocate 2911 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p17 : resolveAt exactSites 2953 = some (AXPushParam.relocate 2911 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2936_p18 : resolveAt exactSites 2954 = some (AXPushParam.relocate 2911 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2936_p : AXPushParam.Bound exactSites 2911 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2936_p0
  · exact row2936_p1
  · exact row2936_p2
  · exact row2936_p3
  · exact row2936_p4
  · exact row2936_p5
  · exact row2936_p6
  · exact row2936_p7
  · exact row2936_p8
  · exact row2936_p9
  · exact row2936_p10
  · exact row2936_p11
  · exact row2936_p12
  · exact row2936_p13
  · exact row2936_p14
  · exact row2936_p15
  · exact row2936_p16
  · exact row2936_p17
  · exact row2936_p18
theorem block2936 : AXMacro.Realizes exactSites .push 2936 2955 :=
  AXMacro.push_realizes bound2936_p
private theorem row2955_c0 : resolveAt exactSites 2955 = some (CopyToT.expected 4 2955 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2955_c1 : resolveAt exactSites 2956 = some (CopyToT.expected 4 2955 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2955_c2 : resolveAt exactSites 2957 = some (CopyToT.expected 4 2955 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2955_c3 : resolveAt exactSites 2958 = some (CopyToT.expected 4 2955 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2955_c4 : resolveAt exactSites 2959 = some (CopyToT.expected 4 2955 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2955_c5 : resolveAt exactSites 2960 = some (CopyToT.expected 4 2955 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2955_c6 : resolveAt exactSites 2961 = some (CopyToT.expected 4 2955 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2955_c : CopyToT.Bound exactSites 4 2955 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2955_c0
  · exact row2955_c1
  · exact row2955_c2
  · exact row2955_c3
  · exact row2955_c4
  · exact row2955_c5
  · exact row2955_c6
theorem block2955 : AXMacro.Realizes exactSites .copyD 2955 2962 :=
  AXMacro.copyD_realizes bound2955_c
private theorem row2962_p0 : resolveAt exactSites 2962 = some (AXPushParam.relocate 2937 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p1 : resolveAt exactSites 2963 = some (AXPushParam.relocate 2937 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p2 : resolveAt exactSites 2964 = some (AXPushParam.relocate 2937 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p3 : resolveAt exactSites 2965 = some (AXPushParam.relocate 2937 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p4 : resolveAt exactSites 2966 = some (AXPushParam.relocate 2937 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p5 : resolveAt exactSites 2967 = some (AXPushParam.relocate 2937 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p6 : resolveAt exactSites 2968 = some (AXPushParam.relocate 2937 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p7 : resolveAt exactSites 2969 = some (AXPushParam.relocate 2937 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p8 : resolveAt exactSites 2970 = some (AXPushParam.relocate 2937 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p9 : resolveAt exactSites 2971 = some (AXPushParam.relocate 2937 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p10 : resolveAt exactSites 2972 = some (AXPushParam.relocate 2937 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p11 : resolveAt exactSites 2973 = some (AXPushParam.relocate 2937 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p12 : resolveAt exactSites 2974 = some (AXPushParam.relocate 2937 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p13 : resolveAt exactSites 2975 = some (AXPushParam.relocate 2937 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p14 : resolveAt exactSites 2976 = some (AXPushParam.relocate 2937 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p15 : resolveAt exactSites 2977 = some (AXPushParam.relocate 2937 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p16 : resolveAt exactSites 2978 = some (AXPushParam.relocate 2937 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p17 : resolveAt exactSites 2979 = some (AXPushParam.relocate 2937 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2962_p18 : resolveAt exactSites 2980 = some (AXPushParam.relocate 2937 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2962_p : AXPushParam.Bound exactSites 2937 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2962_p0
  · exact row2962_p1
  · exact row2962_p2
  · exact row2962_p3
  · exact row2962_p4
  · exact row2962_p5
  · exact row2962_p6
  · exact row2962_p7
  · exact row2962_p8
  · exact row2962_p9
  · exact row2962_p10
  · exact row2962_p11
  · exact row2962_p12
  · exact row2962_p13
  · exact row2962_p14
  · exact row2962_p15
  · exact row2962_p16
  · exact row2962_p17
  · exact row2962_p18
theorem block2962 : AXMacro.Realizes exactSites .push 2962 2981 :=
  AXMacro.push_realizes bound2962_p
private theorem row2981_c0 : resolveAt exactSites 2981 = some (CopyToT.expected 5 2981 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2981_c1 : resolveAt exactSites 2982 = some (CopyToT.expected 5 2981 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2981_c2 : resolveAt exactSites 2983 = some (CopyToT.expected 5 2981 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2981_c3 : resolveAt exactSites 2984 = some (CopyToT.expected 5 2981 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2981_c4 : resolveAt exactSites 2985 = some (CopyToT.expected 5 2981 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2981_c5 : resolveAt exactSites 2986 = some (CopyToT.expected 5 2981 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2981_c6 : resolveAt exactSites 2987 = some (CopyToT.expected 5 2981 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2981_c : CopyToT.Bound exactSites 5 2981 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2981_c0
  · exact row2981_c1
  · exact row2981_c2
  · exact row2981_c3
  · exact row2981_c4
  · exact row2981_c5
  · exact row2981_c6
theorem block2981 : AXMacro.Realizes exactSites .copyH 2981 2988 :=
  AXMacro.copyH_realizes bound2981_c
private theorem row2988_u0 : resolveAt exactSites 2988 = some (UnpairPartial.expected 2988 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_u1 : resolveAt exactSites 2989 = some (UnpairPartial.expected 2988 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_u2 : resolveAt exactSites 2990 = some (UnpairPartial.expected 2988 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_u3 : resolveAt exactSites 2991 = some (UnpairPartial.expected 2988 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_u4 : resolveAt exactSites 2992 = some (UnpairPartial.expected 2988 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_u5 : resolveAt exactSites 2993 = some (UnpairPartial.expected 2988 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_u6 : resolveAt exactSites 2994 = some (UnpairPartial.expected 2988 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_u7 : resolveAt exactSites 2995 = some (UnpairPartial.expected 2988 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_u8 : resolveAt exactSites 2996 = some (UnpairPartial.expected 2988 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_u9 : resolveAt exactSites 2997 = some (UnpairPartial.expected 2988 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_u10 : resolveAt exactSites 2998 = some (UnpairPartial.expected 2988 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2988_u : UnpairPartial.Bound exactSites 2988 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2988_u0
  · exact row2988_u1
  · exact row2988_u2
  · exact row2988_u3
  · exact row2988_u4
  · exact row2988_u5
  · exact row2988_u6
  · exact row2988_u7
  · exact row2988_u8
  · exact row2988_u9
  · exact row2988_u10
private theorem row2988_q0 : resolveAt exactSites 2999 = some (AXPair.relocate 2968 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_q1 : resolveAt exactSites 3000 = some (AXPair.relocate 2968 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_q2 : resolveAt exactSites 3001 = some (AXPair.relocate 2968 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_q3 : resolveAt exactSites 3002 = some (AXPair.relocate 2968 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_q4 : resolveAt exactSites 3003 = some (AXPair.relocate 2968 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_q5 : resolveAt exactSites 3004 = some (AXPair.relocate 2968 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_q6 : resolveAt exactSites 3005 = some (AXPair.relocate 2968 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_q7 : resolveAt exactSites 3006 = some (AXPair.relocate 2968 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_q8 : resolveAt exactSites 3007 = some (AXPair.relocate 2968 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_q9 : resolveAt exactSites 3008 = some (AXPair.relocate 2968 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2988_q : AXPair.Bound exactSites 2968 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2988_q0
  · exact row2988_q1
  · exact row2988_q2
  · exact row2988_q3
  · exact row2988_q4
  · exact row2988_q5
  · exact row2988_q6
  · exact row2988_q7
  · exact row2988_q8
  · exact row2988_q9
private theorem row2988_m0 : resolveAt exactSites 3009 = some (AXTimes4.expected 3009 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_m1 : resolveAt exactSites 3010 = some (AXTimes4.expected 3009 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_m2 : resolveAt exactSites 3011 = some (AXTimes4.expected 3009 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_m3 : resolveAt exactSites 3012 = some (AXTimes4.expected 3009 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_m4 : resolveAt exactSites 3013 = some (AXTimes4.expected 3009 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2988_m5 : resolveAt exactSites 3014 = some (AXTimes4.expected 3009 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2988_m : AXTimes4.Bound exactSites 3009 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2988_m0
  · exact row2988_m1
  · exact row2988_m2
  · exact row2988_m3
  · exact row2988_m4
  · exact row2988_m5
theorem block2988 : AXMacro.Realizes exactSites .cons 2988 3015 :=
  AXMacro.cons_realizes bound2988_u bound2988_q bound2988_m
private theorem row3015_i0 : resolveAt exactSites 3015 = some (Instruction.inc 1 (some 3016)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block3015 : AXMacro.Realizes exactSites .incT 3015 3016 :=
  AXMacro.inc_realizes row3015_i0
private theorem row3016_p0 : resolveAt exactSites 3016 = some (AXPushParam.relocate 2991 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p1 : resolveAt exactSites 3017 = some (AXPushParam.relocate 2991 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p2 : resolveAt exactSites 3018 = some (AXPushParam.relocate 2991 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p3 : resolveAt exactSites 3019 = some (AXPushParam.relocate 2991 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p4 : resolveAt exactSites 3020 = some (AXPushParam.relocate 2991 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p5 : resolveAt exactSites 3021 = some (AXPushParam.relocate 2991 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p6 : resolveAt exactSites 3022 = some (AXPushParam.relocate 2991 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p7 : resolveAt exactSites 3023 = some (AXPushParam.relocate 2991 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p8 : resolveAt exactSites 3024 = some (AXPushParam.relocate 2991 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p9 : resolveAt exactSites 3025 = some (AXPushParam.relocate 2991 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p10 : resolveAt exactSites 3026 = some (AXPushParam.relocate 2991 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p11 : resolveAt exactSites 3027 = some (AXPushParam.relocate 2991 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p12 : resolveAt exactSites 3028 = some (AXPushParam.relocate 2991 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p13 : resolveAt exactSites 3029 = some (AXPushParam.relocate 2991 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p14 : resolveAt exactSites 3030 = some (AXPushParam.relocate 2991 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p15 : resolveAt exactSites 3031 = some (AXPushParam.relocate 2991 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p16 : resolveAt exactSites 3032 = some (AXPushParam.relocate 2991 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p17 : resolveAt exactSites 3033 = some (AXPushParam.relocate 2991 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3016_p18 : resolveAt exactSites 3034 = some (AXPushParam.relocate 2991 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3016_p : AXPushParam.Bound exactSites 2991 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3016_p0
  · exact row3016_p1
  · exact row3016_p2
  · exact row3016_p3
  · exact row3016_p4
  · exact row3016_p5
  · exact row3016_p6
  · exact row3016_p7
  · exact row3016_p8
  · exact row3016_p9
  · exact row3016_p10
  · exact row3016_p11
  · exact row3016_p12
  · exact row3016_p13
  · exact row3016_p14
  · exact row3016_p15
  · exact row3016_p16
  · exact row3016_p17
  · exact row3016_p18
theorem block3016 : AXMacro.Realizes exactSites .push 3016 3035 :=
  AXMacro.push_realizes bound3016_p
def code018 : List AXMacro.Op := [.cons,.push,.copyA,.push,.copyH,.push,.copyD,.push,.copyH,.cons,.incT,.push]
theorem plan018 : AXMacro.Plan exactSites 2857 3035 code018 :=
  AXMacro.Plan.cons block2857 ( AXMacro.Plan.cons block2884 ( AXMacro.Plan.cons block2903 ( AXMacro.Plan.cons block2910 ( AXMacro.Plan.cons block2929 ( AXMacro.Plan.cons block2936 ( AXMacro.Plan.cons block2955 ( AXMacro.Plan.cons block2962 ( AXMacro.Plan.cons block2981 ( AXMacro.Plan.cons block2988 ( AXMacro.Plan.cons block3015 ( AXMacro.Plan.cons block3016 ( AXMacro.Plan.nil 3035))))))))))))
#print axioms plan018
end M6.Source.AXAll

