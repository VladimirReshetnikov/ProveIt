module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row3035_c0 : resolveAt exactSites 3035 = some (CopyToT.expected 3 3035 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3035_c1 : resolveAt exactSites 3036 = some (CopyToT.expected 3 3035 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3035_c2 : resolveAt exactSites 3037 = some (CopyToT.expected 3 3035 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3035_c3 : resolveAt exactSites 3038 = some (CopyToT.expected 3 3035 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3035_c4 : resolveAt exactSites 3039 = some (CopyToT.expected 3 3035 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3035_c5 : resolveAt exactSites 3040 = some (CopyToT.expected 3 3035 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3035_c6 : resolveAt exactSites 3041 = some (CopyToT.expected 3 3035 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3035_c : CopyToT.Bound exactSites 3 3035 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3035_c0
  · exact row3035_c1
  · exact row3035_c2
  · exact row3035_c3
  · exact row3035_c4
  · exact row3035_c5
  · exact row3035_c6
theorem block3035 : AXMacro.Realizes exactSites .copyA 3035 3042 :=
  AXMacro.copyA_realizes bound3035_c
private theorem row3042_p0 : resolveAt exactSites 3042 = some (AXPushParam.relocate 3017 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p1 : resolveAt exactSites 3043 = some (AXPushParam.relocate 3017 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p2 : resolveAt exactSites 3044 = some (AXPushParam.relocate 3017 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p3 : resolveAt exactSites 3045 = some (AXPushParam.relocate 3017 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p4 : resolveAt exactSites 3046 = some (AXPushParam.relocate 3017 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p5 : resolveAt exactSites 3047 = some (AXPushParam.relocate 3017 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p6 : resolveAt exactSites 3048 = some (AXPushParam.relocate 3017 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p7 : resolveAt exactSites 3049 = some (AXPushParam.relocate 3017 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p8 : resolveAt exactSites 3050 = some (AXPushParam.relocate 3017 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p9 : resolveAt exactSites 3051 = some (AXPushParam.relocate 3017 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p10 : resolveAt exactSites 3052 = some (AXPushParam.relocate 3017 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p11 : resolveAt exactSites 3053 = some (AXPushParam.relocate 3017 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p12 : resolveAt exactSites 3054 = some (AXPushParam.relocate 3017 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p13 : resolveAt exactSites 3055 = some (AXPushParam.relocate 3017 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p14 : resolveAt exactSites 3056 = some (AXPushParam.relocate 3017 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p15 : resolveAt exactSites 3057 = some (AXPushParam.relocate 3017 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p16 : resolveAt exactSites 3058 = some (AXPushParam.relocate 3017 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p17 : resolveAt exactSites 3059 = some (AXPushParam.relocate 3017 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3042_p18 : resolveAt exactSites 3060 = some (AXPushParam.relocate 3017 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3042_p : AXPushParam.Bound exactSites 3017 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3042_p0
  · exact row3042_p1
  · exact row3042_p2
  · exact row3042_p3
  · exact row3042_p4
  · exact row3042_p5
  · exact row3042_p6
  · exact row3042_p7
  · exact row3042_p8
  · exact row3042_p9
  · exact row3042_p10
  · exact row3042_p11
  · exact row3042_p12
  · exact row3042_p13
  · exact row3042_p14
  · exact row3042_p15
  · exact row3042_p16
  · exact row3042_p17
  · exact row3042_p18
theorem block3042 : AXMacro.Realizes exactSites .push 3042 3061 :=
  AXMacro.push_realizes bound3042_p
private theorem row3061_c0 : resolveAt exactSites 3061 = some (CopyToT.expected 3 3061 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3061_c1 : resolveAt exactSites 3062 = some (CopyToT.expected 3 3061 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3061_c2 : resolveAt exactSites 3063 = some (CopyToT.expected 3 3061 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3061_c3 : resolveAt exactSites 3064 = some (CopyToT.expected 3 3061 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3061_c4 : resolveAt exactSites 3065 = some (CopyToT.expected 3 3061 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3061_c5 : resolveAt exactSites 3066 = some (CopyToT.expected 3 3061 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3061_c6 : resolveAt exactSites 3067 = some (CopyToT.expected 3 3061 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3061_c : CopyToT.Bound exactSites 3 3061 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3061_c0
  · exact row3061_c1
  · exact row3061_c2
  · exact row3061_c3
  · exact row3061_c4
  · exact row3061_c5
  · exact row3061_c6
theorem block3061 : AXMacro.Realizes exactSites .copyA 3061 3068 :=
  AXMacro.copyA_realizes bound3061_c
private theorem row3068_p0 : resolveAt exactSites 3068 = some (AXPushParam.relocate 3043 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p1 : resolveAt exactSites 3069 = some (AXPushParam.relocate 3043 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p2 : resolveAt exactSites 3070 = some (AXPushParam.relocate 3043 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p3 : resolveAt exactSites 3071 = some (AXPushParam.relocate 3043 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p4 : resolveAt exactSites 3072 = some (AXPushParam.relocate 3043 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p5 : resolveAt exactSites 3073 = some (AXPushParam.relocate 3043 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p6 : resolveAt exactSites 3074 = some (AXPushParam.relocate 3043 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p7 : resolveAt exactSites 3075 = some (AXPushParam.relocate 3043 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p8 : resolveAt exactSites 3076 = some (AXPushParam.relocate 3043 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p9 : resolveAt exactSites 3077 = some (AXPushParam.relocate 3043 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p10 : resolveAt exactSites 3078 = some (AXPushParam.relocate 3043 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p11 : resolveAt exactSites 3079 = some (AXPushParam.relocate 3043 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p12 : resolveAt exactSites 3080 = some (AXPushParam.relocate 3043 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p13 : resolveAt exactSites 3081 = some (AXPushParam.relocate 3043 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p14 : resolveAt exactSites 3082 = some (AXPushParam.relocate 3043 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p15 : resolveAt exactSites 3083 = some (AXPushParam.relocate 3043 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p16 : resolveAt exactSites 3084 = some (AXPushParam.relocate 3043 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p17 : resolveAt exactSites 3085 = some (AXPushParam.relocate 3043 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3068_p18 : resolveAt exactSites 3086 = some (AXPushParam.relocate 3043 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3068_p : AXPushParam.Bound exactSites 3043 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3068_p0
  · exact row3068_p1
  · exact row3068_p2
  · exact row3068_p3
  · exact row3068_p4
  · exact row3068_p5
  · exact row3068_p6
  · exact row3068_p7
  · exact row3068_p8
  · exact row3068_p9
  · exact row3068_p10
  · exact row3068_p11
  · exact row3068_p12
  · exact row3068_p13
  · exact row3068_p14
  · exact row3068_p15
  · exact row3068_p16
  · exact row3068_p17
  · exact row3068_p18
theorem block3068 : AXMacro.Realizes exactSites .push 3068 3087 :=
  AXMacro.push_realizes bound3068_p
private theorem row3087_c0 : resolveAt exactSites 3087 = some (CopyToT.expected 5 3087 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3087_c1 : resolveAt exactSites 3088 = some (CopyToT.expected 5 3087 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3087_c2 : resolveAt exactSites 3089 = some (CopyToT.expected 5 3087 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3087_c3 : resolveAt exactSites 3090 = some (CopyToT.expected 5 3087 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3087_c4 : resolveAt exactSites 3091 = some (CopyToT.expected 5 3087 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3087_c5 : resolveAt exactSites 3092 = some (CopyToT.expected 5 3087 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3087_c6 : resolveAt exactSites 3093 = some (CopyToT.expected 5 3087 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3087_c : CopyToT.Bound exactSites 5 3087 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3087_c0
  · exact row3087_c1
  · exact row3087_c2
  · exact row3087_c3
  · exact row3087_c4
  · exact row3087_c5
  · exact row3087_c6
theorem block3087 : AXMacro.Realizes exactSites .copyH 3087 3094 :=
  AXMacro.copyH_realizes bound3087_c
private theorem row3094_u0 : resolveAt exactSites 3094 = some (UnpairPartial.expected 3094 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_u1 : resolveAt exactSites 3095 = some (UnpairPartial.expected 3094 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_u2 : resolveAt exactSites 3096 = some (UnpairPartial.expected 3094 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_u3 : resolveAt exactSites 3097 = some (UnpairPartial.expected 3094 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_u4 : resolveAt exactSites 3098 = some (UnpairPartial.expected 3094 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_u5 : resolveAt exactSites 3099 = some (UnpairPartial.expected 3094 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_u6 : resolveAt exactSites 3100 = some (UnpairPartial.expected 3094 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_u7 : resolveAt exactSites 3101 = some (UnpairPartial.expected 3094 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_u8 : resolveAt exactSites 3102 = some (UnpairPartial.expected 3094 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_u9 : resolveAt exactSites 3103 = some (UnpairPartial.expected 3094 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_u10 : resolveAt exactSites 3104 = some (UnpairPartial.expected 3094 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3094_u : UnpairPartial.Bound exactSites 3094 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3094_u0
  · exact row3094_u1
  · exact row3094_u2
  · exact row3094_u3
  · exact row3094_u4
  · exact row3094_u5
  · exact row3094_u6
  · exact row3094_u7
  · exact row3094_u8
  · exact row3094_u9
  · exact row3094_u10
private theorem row3094_q0 : resolveAt exactSites 3105 = some (AXPair.relocate 3074 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_q1 : resolveAt exactSites 3106 = some (AXPair.relocate 3074 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_q2 : resolveAt exactSites 3107 = some (AXPair.relocate 3074 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_q3 : resolveAt exactSites 3108 = some (AXPair.relocate 3074 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_q4 : resolveAt exactSites 3109 = some (AXPair.relocate 3074 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_q5 : resolveAt exactSites 3110 = some (AXPair.relocate 3074 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_q6 : resolveAt exactSites 3111 = some (AXPair.relocate 3074 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_q7 : resolveAt exactSites 3112 = some (AXPair.relocate 3074 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_q8 : resolveAt exactSites 3113 = some (AXPair.relocate 3074 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_q9 : resolveAt exactSites 3114 = some (AXPair.relocate 3074 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3094_q : AXPair.Bound exactSites 3074 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3094_q0
  · exact row3094_q1
  · exact row3094_q2
  · exact row3094_q3
  · exact row3094_q4
  · exact row3094_q5
  · exact row3094_q6
  · exact row3094_q7
  · exact row3094_q8
  · exact row3094_q9
private theorem row3094_m0 : resolveAt exactSites 3115 = some (AXTimes4.expected 3115 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_m1 : resolveAt exactSites 3116 = some (AXTimes4.expected 3115 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_m2 : resolveAt exactSites 3117 = some (AXTimes4.expected 3115 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_m3 : resolveAt exactSites 3118 = some (AXTimes4.expected 3115 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_m4 : resolveAt exactSites 3119 = some (AXTimes4.expected 3115 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3094_m5 : resolveAt exactSites 3120 = some (AXTimes4.expected 3115 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3094_m : AXTimes4.Bound exactSites 3115 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3094_m0
  · exact row3094_m1
  · exact row3094_m2
  · exact row3094_m3
  · exact row3094_m4
  · exact row3094_m5
theorem block3094 : AXMacro.Realizes exactSites .cons 3094 3121 :=
  AXMacro.cons_realizes bound3094_u bound3094_q bound3094_m
private theorem row3121_i0 : resolveAt exactSites 3121 = some (Instruction.inc 1 (some 3122)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block3121 : AXMacro.Realizes exactSites .incT 3121 3122 :=
  AXMacro.inc_realizes row3121_i0
private theorem row3122_u0 : resolveAt exactSites 3122 = some (UnpairPartial.expected 3122 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_u1 : resolveAt exactSites 3123 = some (UnpairPartial.expected 3122 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_u2 : resolveAt exactSites 3124 = some (UnpairPartial.expected 3122 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_u3 : resolveAt exactSites 3125 = some (UnpairPartial.expected 3122 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_u4 : resolveAt exactSites 3126 = some (UnpairPartial.expected 3122 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_u5 : resolveAt exactSites 3127 = some (UnpairPartial.expected 3122 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_u6 : resolveAt exactSites 3128 = some (UnpairPartial.expected 3122 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_u7 : resolveAt exactSites 3129 = some (UnpairPartial.expected 3122 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_u8 : resolveAt exactSites 3130 = some (UnpairPartial.expected 3122 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_u9 : resolveAt exactSites 3131 = some (UnpairPartial.expected 3122 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_u10 : resolveAt exactSites 3132 = some (UnpairPartial.expected 3122 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3122_u : UnpairPartial.Bound exactSites 3122 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3122_u0
  · exact row3122_u1
  · exact row3122_u2
  · exact row3122_u3
  · exact row3122_u4
  · exact row3122_u5
  · exact row3122_u6
  · exact row3122_u7
  · exact row3122_u8
  · exact row3122_u9
  · exact row3122_u10
private theorem row3122_q0 : resolveAt exactSites 3133 = some (AXPair.relocate 3102 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_q1 : resolveAt exactSites 3134 = some (AXPair.relocate 3102 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_q2 : resolveAt exactSites 3135 = some (AXPair.relocate 3102 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_q3 : resolveAt exactSites 3136 = some (AXPair.relocate 3102 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_q4 : resolveAt exactSites 3137 = some (AXPair.relocate 3102 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_q5 : resolveAt exactSites 3138 = some (AXPair.relocate 3102 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_q6 : resolveAt exactSites 3139 = some (AXPair.relocate 3102 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_q7 : resolveAt exactSites 3140 = some (AXPair.relocate 3102 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_q8 : resolveAt exactSites 3141 = some (AXPair.relocate 3102 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_q9 : resolveAt exactSites 3142 = some (AXPair.relocate 3102 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3122_q : AXPair.Bound exactSites 3102 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3122_q0
  · exact row3122_q1
  · exact row3122_q2
  · exact row3122_q3
  · exact row3122_q4
  · exact row3122_q5
  · exact row3122_q6
  · exact row3122_q7
  · exact row3122_q8
  · exact row3122_q9
private theorem row3122_m0 : resolveAt exactSites 3143 = some (AXTimes4.expected 3143 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_m1 : resolveAt exactSites 3144 = some (AXTimes4.expected 3143 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_m2 : resolveAt exactSites 3145 = some (AXTimes4.expected 3143 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_m3 : resolveAt exactSites 3146 = some (AXTimes4.expected 3143 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_m4 : resolveAt exactSites 3147 = some (AXTimes4.expected 3143 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3122_m5 : resolveAt exactSites 3148 = some (AXTimes4.expected 3143 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3122_m : AXTimes4.Bound exactSites 3143 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3122_m0
  · exact row3122_m1
  · exact row3122_m2
  · exact row3122_m3
  · exact row3122_m4
  · exact row3122_m5
theorem block3122 : AXMacro.Realizes exactSites .cons 3122 3149 :=
  AXMacro.cons_realizes bound3122_u bound3122_q bound3122_m
private theorem row3149_u0 : resolveAt exactSites 3149 = some (UnpairPartial.expected 3149 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_u1 : resolveAt exactSites 3150 = some (UnpairPartial.expected 3149 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_u2 : resolveAt exactSites 3151 = some (UnpairPartial.expected 3149 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_u3 : resolveAt exactSites 3152 = some (UnpairPartial.expected 3149 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_u4 : resolveAt exactSites 3153 = some (UnpairPartial.expected 3149 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_u5 : resolveAt exactSites 3154 = some (UnpairPartial.expected 3149 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_u6 : resolveAt exactSites 3155 = some (UnpairPartial.expected 3149 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_u7 : resolveAt exactSites 3156 = some (UnpairPartial.expected 3149 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_u8 : resolveAt exactSites 3157 = some (UnpairPartial.expected 3149 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_u9 : resolveAt exactSites 3158 = some (UnpairPartial.expected 3149 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_u10 : resolveAt exactSites 3159 = some (UnpairPartial.expected 3149 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3149_u : UnpairPartial.Bound exactSites 3149 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3149_u0
  · exact row3149_u1
  · exact row3149_u2
  · exact row3149_u3
  · exact row3149_u4
  · exact row3149_u5
  · exact row3149_u6
  · exact row3149_u7
  · exact row3149_u8
  · exact row3149_u9
  · exact row3149_u10
private theorem row3149_q0 : resolveAt exactSites 3160 = some (AXPair.relocate 3129 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_q1 : resolveAt exactSites 3161 = some (AXPair.relocate 3129 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_q2 : resolveAt exactSites 3162 = some (AXPair.relocate 3129 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_q3 : resolveAt exactSites 3163 = some (AXPair.relocate 3129 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_q4 : resolveAt exactSites 3164 = some (AXPair.relocate 3129 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_q5 : resolveAt exactSites 3165 = some (AXPair.relocate 3129 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_q6 : resolveAt exactSites 3166 = some (AXPair.relocate 3129 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_q7 : resolveAt exactSites 3167 = some (AXPair.relocate 3129 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_q8 : resolveAt exactSites 3168 = some (AXPair.relocate 3129 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_q9 : resolveAt exactSites 3169 = some (AXPair.relocate 3129 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3149_q : AXPair.Bound exactSites 3129 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3149_q0
  · exact row3149_q1
  · exact row3149_q2
  · exact row3149_q3
  · exact row3149_q4
  · exact row3149_q5
  · exact row3149_q6
  · exact row3149_q7
  · exact row3149_q8
  · exact row3149_q9
private theorem row3149_m0 : resolveAt exactSites 3170 = some (AXTimes4.expected 3170 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_m1 : resolveAt exactSites 3171 = some (AXTimes4.expected 3170 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_m2 : resolveAt exactSites 3172 = some (AXTimes4.expected 3170 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_m3 : resolveAt exactSites 3173 = some (AXTimes4.expected 3170 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_m4 : resolveAt exactSites 3174 = some (AXTimes4.expected 3170 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3149_m5 : resolveAt exactSites 3175 = some (AXTimes4.expected 3170 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3149_m : AXTimes4.Bound exactSites 3170 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3149_m0
  · exact row3149_m1
  · exact row3149_m2
  · exact row3149_m3
  · exact row3149_m4
  · exact row3149_m5
theorem block3149 : AXMacro.Realizes exactSites .cons 3149 3176 :=
  AXMacro.cons_realizes bound3149_u bound3149_q bound3149_m
private theorem row3176_p0 : resolveAt exactSites 3176 = some (AXPushParam.relocate 3151 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p1 : resolveAt exactSites 3177 = some (AXPushParam.relocate 3151 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p2 : resolveAt exactSites 3178 = some (AXPushParam.relocate 3151 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p3 : resolveAt exactSites 3179 = some (AXPushParam.relocate 3151 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p4 : resolveAt exactSites 3180 = some (AXPushParam.relocate 3151 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p5 : resolveAt exactSites 3181 = some (AXPushParam.relocate 3151 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p6 : resolveAt exactSites 3182 = some (AXPushParam.relocate 3151 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p7 : resolveAt exactSites 3183 = some (AXPushParam.relocate 3151 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p8 : resolveAt exactSites 3184 = some (AXPushParam.relocate 3151 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p9 : resolveAt exactSites 3185 = some (AXPushParam.relocate 3151 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p10 : resolveAt exactSites 3186 = some (AXPushParam.relocate 3151 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p11 : resolveAt exactSites 3187 = some (AXPushParam.relocate 3151 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p12 : resolveAt exactSites 3188 = some (AXPushParam.relocate 3151 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p13 : resolveAt exactSites 3189 = some (AXPushParam.relocate 3151 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p14 : resolveAt exactSites 3190 = some (AXPushParam.relocate 3151 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p15 : resolveAt exactSites 3191 = some (AXPushParam.relocate 3151 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p16 : resolveAt exactSites 3192 = some (AXPushParam.relocate 3151 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p17 : resolveAt exactSites 3193 = some (AXPushParam.relocate 3151 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3176_p18 : resolveAt exactSites 3194 = some (AXPushParam.relocate 3151 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3176_p : AXPushParam.Bound exactSites 3151 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3176_p0
  · exact row3176_p1
  · exact row3176_p2
  · exact row3176_p3
  · exact row3176_p4
  · exact row3176_p5
  · exact row3176_p6
  · exact row3176_p7
  · exact row3176_p8
  · exact row3176_p9
  · exact row3176_p10
  · exact row3176_p11
  · exact row3176_p12
  · exact row3176_p13
  · exact row3176_p14
  · exact row3176_p15
  · exact row3176_p16
  · exact row3176_p17
  · exact row3176_p18
theorem block3176 : AXMacro.Realizes exactSites .push 3176 3195 :=
  AXMacro.push_realizes bound3176_p
private theorem row3195_c0 : resolveAt exactSites 3195 = some (CopyToT.expected 3 3195 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3195_c1 : resolveAt exactSites 3196 = some (CopyToT.expected 3 3195 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3195_c2 : resolveAt exactSites 3197 = some (CopyToT.expected 3 3195 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3195_c3 : resolveAt exactSites 3198 = some (CopyToT.expected 3 3195 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3195_c4 : resolveAt exactSites 3199 = some (CopyToT.expected 3 3195 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3195_c5 : resolveAt exactSites 3200 = some (CopyToT.expected 3 3195 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3195_c6 : resolveAt exactSites 3201 = some (CopyToT.expected 3 3195 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3195_c : CopyToT.Bound exactSites 3 3195 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3195_c0
  · exact row3195_c1
  · exact row3195_c2
  · exact row3195_c3
  · exact row3195_c4
  · exact row3195_c5
  · exact row3195_c6
theorem block3195 : AXMacro.Realizes exactSites .copyA 3195 3202 :=
  AXMacro.copyA_realizes bound3195_c
private theorem row3202_p0 : resolveAt exactSites 3202 = some (AXPushParam.relocate 3177 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p1 : resolveAt exactSites 3203 = some (AXPushParam.relocate 3177 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p2 : resolveAt exactSites 3204 = some (AXPushParam.relocate 3177 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p3 : resolveAt exactSites 3205 = some (AXPushParam.relocate 3177 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p4 : resolveAt exactSites 3206 = some (AXPushParam.relocate 3177 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p5 : resolveAt exactSites 3207 = some (AXPushParam.relocate 3177 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p6 : resolveAt exactSites 3208 = some (AXPushParam.relocate 3177 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p7 : resolveAt exactSites 3209 = some (AXPushParam.relocate 3177 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p8 : resolveAt exactSites 3210 = some (AXPushParam.relocate 3177 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p9 : resolveAt exactSites 3211 = some (AXPushParam.relocate 3177 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p10 : resolveAt exactSites 3212 = some (AXPushParam.relocate 3177 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p11 : resolveAt exactSites 3213 = some (AXPushParam.relocate 3177 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p12 : resolveAt exactSites 3214 = some (AXPushParam.relocate 3177 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p13 : resolveAt exactSites 3215 = some (AXPushParam.relocate 3177 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p14 : resolveAt exactSites 3216 = some (AXPushParam.relocate 3177 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p15 : resolveAt exactSites 3217 = some (AXPushParam.relocate 3177 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p16 : resolveAt exactSites 3218 = some (AXPushParam.relocate 3177 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p17 : resolveAt exactSites 3219 = some (AXPushParam.relocate 3177 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3202_p18 : resolveAt exactSites 3220 = some (AXPushParam.relocate 3177 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3202_p : AXPushParam.Bound exactSites 3177 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3202_p0
  · exact row3202_p1
  · exact row3202_p2
  · exact row3202_p3
  · exact row3202_p4
  · exact row3202_p5
  · exact row3202_p6
  · exact row3202_p7
  · exact row3202_p8
  · exact row3202_p9
  · exact row3202_p10
  · exact row3202_p11
  · exact row3202_p12
  · exact row3202_p13
  · exact row3202_p14
  · exact row3202_p15
  · exact row3202_p16
  · exact row3202_p17
  · exact row3202_p18
theorem block3202 : AXMacro.Realizes exactSites .push 3202 3221 :=
  AXMacro.push_realizes bound3202_p
def code019 : List AXMacro.Op := [.copyA,.push,.copyA,.push,.copyH,.cons,.incT,.cons,.cons,.push,.copyA,.push]
theorem plan019 : AXMacro.Plan exactSites 3035 3221 code019 :=
  AXMacro.Plan.cons block3035 ( AXMacro.Plan.cons block3042 ( AXMacro.Plan.cons block3061 ( AXMacro.Plan.cons block3068 ( AXMacro.Plan.cons block3087 ( AXMacro.Plan.cons block3094 ( AXMacro.Plan.cons block3121 ( AXMacro.Plan.cons block3122 ( AXMacro.Plan.cons block3149 ( AXMacro.Plan.cons block3176 ( AXMacro.Plan.cons block3195 ( AXMacro.Plan.cons block3202 ( AXMacro.Plan.nil 3221))))))))))))
#print axioms plan019
end M6.Source.AXAll

