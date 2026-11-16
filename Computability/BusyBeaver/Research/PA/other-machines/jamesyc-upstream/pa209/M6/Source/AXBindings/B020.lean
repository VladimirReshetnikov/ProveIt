module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row3221_c0 : resolveAt exactSites 3221 = some (CopyToT.expected 5 3221 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3221_c1 : resolveAt exactSites 3222 = some (CopyToT.expected 5 3221 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3221_c2 : resolveAt exactSites 3223 = some (CopyToT.expected 5 3221 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3221_c3 : resolveAt exactSites 3224 = some (CopyToT.expected 5 3221 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3221_c4 : resolveAt exactSites 3225 = some (CopyToT.expected 5 3221 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3221_c5 : resolveAt exactSites 3226 = some (CopyToT.expected 5 3221 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3221_c6 : resolveAt exactSites 3227 = some (CopyToT.expected 5 3221 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3221_c : CopyToT.Bound exactSites 5 3221 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3221_c0
  · exact row3221_c1
  · exact row3221_c2
  · exact row3221_c3
  · exact row3221_c4
  · exact row3221_c5
  · exact row3221_c6
theorem block3221 : AXMacro.Realizes exactSites .copyH 3221 3228 :=
  AXMacro.copyH_realizes bound3221_c
private theorem row3228_u0 : resolveAt exactSites 3228 = some (UnpairPartial.expected 3228 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_u1 : resolveAt exactSites 3229 = some (UnpairPartial.expected 3228 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_u2 : resolveAt exactSites 3230 = some (UnpairPartial.expected 3228 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_u3 : resolveAt exactSites 3231 = some (UnpairPartial.expected 3228 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_u4 : resolveAt exactSites 3232 = some (UnpairPartial.expected 3228 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_u5 : resolveAt exactSites 3233 = some (UnpairPartial.expected 3228 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_u6 : resolveAt exactSites 3234 = some (UnpairPartial.expected 3228 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_u7 : resolveAt exactSites 3235 = some (UnpairPartial.expected 3228 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_u8 : resolveAt exactSites 3236 = some (UnpairPartial.expected 3228 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_u9 : resolveAt exactSites 3237 = some (UnpairPartial.expected 3228 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_u10 : resolveAt exactSites 3238 = some (UnpairPartial.expected 3228 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3228_u : UnpairPartial.Bound exactSites 3228 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3228_u0
  · exact row3228_u1
  · exact row3228_u2
  · exact row3228_u3
  · exact row3228_u4
  · exact row3228_u5
  · exact row3228_u6
  · exact row3228_u7
  · exact row3228_u8
  · exact row3228_u9
  · exact row3228_u10
private theorem row3228_q0 : resolveAt exactSites 3239 = some (AXPair.relocate 3208 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_q1 : resolveAt exactSites 3240 = some (AXPair.relocate 3208 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_q2 : resolveAt exactSites 3241 = some (AXPair.relocate 3208 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_q3 : resolveAt exactSites 3242 = some (AXPair.relocate 3208 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_q4 : resolveAt exactSites 3243 = some (AXPair.relocate 3208 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_q5 : resolveAt exactSites 3244 = some (AXPair.relocate 3208 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_q6 : resolveAt exactSites 3245 = some (AXPair.relocate 3208 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_q7 : resolveAt exactSites 3246 = some (AXPair.relocate 3208 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_q8 : resolveAt exactSites 3247 = some (AXPair.relocate 3208 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_q9 : resolveAt exactSites 3248 = some (AXPair.relocate 3208 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3228_q : AXPair.Bound exactSites 3208 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3228_q0
  · exact row3228_q1
  · exact row3228_q2
  · exact row3228_q3
  · exact row3228_q4
  · exact row3228_q5
  · exact row3228_q6
  · exact row3228_q7
  · exact row3228_q8
  · exact row3228_q9
private theorem row3228_m0 : resolveAt exactSites 3249 = some (AXTimes4.expected 3249 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_m1 : resolveAt exactSites 3250 = some (AXTimes4.expected 3249 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_m2 : resolveAt exactSites 3251 = some (AXTimes4.expected 3249 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_m3 : resolveAt exactSites 3252 = some (AXTimes4.expected 3249 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_m4 : resolveAt exactSites 3253 = some (AXTimes4.expected 3249 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3228_m5 : resolveAt exactSites 3254 = some (AXTimes4.expected 3249 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3228_m : AXTimes4.Bound exactSites 3249 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3228_m0
  · exact row3228_m1
  · exact row3228_m2
  · exact row3228_m3
  · exact row3228_m4
  · exact row3228_m5
theorem block3228 : AXMacro.Realizes exactSites .cons 3228 3255 :=
  AXMacro.cons_realizes bound3228_u bound3228_q bound3228_m
private theorem row3255_i0 : resolveAt exactSites 3255 = some (Instruction.inc 1 (some 3256)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block3255 : AXMacro.Realizes exactSites .incT 3255 3256 :=
  AXMacro.inc_realizes row3255_i0
private theorem row3256_p0 : resolveAt exactSites 3256 = some (AXPushParam.relocate 3231 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p1 : resolveAt exactSites 3257 = some (AXPushParam.relocate 3231 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p2 : resolveAt exactSites 3258 = some (AXPushParam.relocate 3231 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p3 : resolveAt exactSites 3259 = some (AXPushParam.relocate 3231 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p4 : resolveAt exactSites 3260 = some (AXPushParam.relocate 3231 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p5 : resolveAt exactSites 3261 = some (AXPushParam.relocate 3231 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p6 : resolveAt exactSites 3262 = some (AXPushParam.relocate 3231 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p7 : resolveAt exactSites 3263 = some (AXPushParam.relocate 3231 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p8 : resolveAt exactSites 3264 = some (AXPushParam.relocate 3231 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p9 : resolveAt exactSites 3265 = some (AXPushParam.relocate 3231 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p10 : resolveAt exactSites 3266 = some (AXPushParam.relocate 3231 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p11 : resolveAt exactSites 3267 = some (AXPushParam.relocate 3231 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p12 : resolveAt exactSites 3268 = some (AXPushParam.relocate 3231 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p13 : resolveAt exactSites 3269 = some (AXPushParam.relocate 3231 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p14 : resolveAt exactSites 3270 = some (AXPushParam.relocate 3231 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p15 : resolveAt exactSites 3271 = some (AXPushParam.relocate 3231 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p16 : resolveAt exactSites 3272 = some (AXPushParam.relocate 3231 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p17 : resolveAt exactSites 3273 = some (AXPushParam.relocate 3231 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3256_p18 : resolveAt exactSites 3274 = some (AXPushParam.relocate 3231 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3256_p : AXPushParam.Bound exactSites 3231 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3256_p0
  · exact row3256_p1
  · exact row3256_p2
  · exact row3256_p3
  · exact row3256_p4
  · exact row3256_p5
  · exact row3256_p6
  · exact row3256_p7
  · exact row3256_p8
  · exact row3256_p9
  · exact row3256_p10
  · exact row3256_p11
  · exact row3256_p12
  · exact row3256_p13
  · exact row3256_p14
  · exact row3256_p15
  · exact row3256_p16
  · exact row3256_p17
  · exact row3256_p18
theorem block3256 : AXMacro.Realizes exactSites .push 3256 3275 :=
  AXMacro.push_realizes bound3256_p
private theorem row3275_c0 : resolveAt exactSites 3275 = some (CopyToT.expected 3 3275 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3275_c1 : resolveAt exactSites 3276 = some (CopyToT.expected 3 3275 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3275_c2 : resolveAt exactSites 3277 = some (CopyToT.expected 3 3275 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3275_c3 : resolveAt exactSites 3278 = some (CopyToT.expected 3 3275 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3275_c4 : resolveAt exactSites 3279 = some (CopyToT.expected 3 3275 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3275_c5 : resolveAt exactSites 3280 = some (CopyToT.expected 3 3275 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3275_c6 : resolveAt exactSites 3281 = some (CopyToT.expected 3 3275 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3275_c : CopyToT.Bound exactSites 3 3275 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3275_c0
  · exact row3275_c1
  · exact row3275_c2
  · exact row3275_c3
  · exact row3275_c4
  · exact row3275_c5
  · exact row3275_c6
theorem block3275 : AXMacro.Realizes exactSites .copyA 3275 3282 :=
  AXMacro.copyA_realizes bound3275_c
private theorem row3282_u0 : resolveAt exactSites 3282 = some (UnpairPartial.expected 3282 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_u1 : resolveAt exactSites 3283 = some (UnpairPartial.expected 3282 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_u2 : resolveAt exactSites 3284 = some (UnpairPartial.expected 3282 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_u3 : resolveAt exactSites 3285 = some (UnpairPartial.expected 3282 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_u4 : resolveAt exactSites 3286 = some (UnpairPartial.expected 3282 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_u5 : resolveAt exactSites 3287 = some (UnpairPartial.expected 3282 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_u6 : resolveAt exactSites 3288 = some (UnpairPartial.expected 3282 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_u7 : resolveAt exactSites 3289 = some (UnpairPartial.expected 3282 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_u8 : resolveAt exactSites 3290 = some (UnpairPartial.expected 3282 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_u9 : resolveAt exactSites 3291 = some (UnpairPartial.expected 3282 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_u10 : resolveAt exactSites 3292 = some (UnpairPartial.expected 3282 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3282_u : UnpairPartial.Bound exactSites 3282 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3282_u0
  · exact row3282_u1
  · exact row3282_u2
  · exact row3282_u3
  · exact row3282_u4
  · exact row3282_u5
  · exact row3282_u6
  · exact row3282_u7
  · exact row3282_u8
  · exact row3282_u9
  · exact row3282_u10
private theorem row3282_q0 : resolveAt exactSites 3293 = some (AXPair.relocate 3262 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_q1 : resolveAt exactSites 3294 = some (AXPair.relocate 3262 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_q2 : resolveAt exactSites 3295 = some (AXPair.relocate 3262 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_q3 : resolveAt exactSites 3296 = some (AXPair.relocate 3262 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_q4 : resolveAt exactSites 3297 = some (AXPair.relocate 3262 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_q5 : resolveAt exactSites 3298 = some (AXPair.relocate 3262 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_q6 : resolveAt exactSites 3299 = some (AXPair.relocate 3262 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_q7 : resolveAt exactSites 3300 = some (AXPair.relocate 3262 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_q8 : resolveAt exactSites 3301 = some (AXPair.relocate 3262 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_q9 : resolveAt exactSites 3302 = some (AXPair.relocate 3262 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3282_q : AXPair.Bound exactSites 3262 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3282_q0
  · exact row3282_q1
  · exact row3282_q2
  · exact row3282_q3
  · exact row3282_q4
  · exact row3282_q5
  · exact row3282_q6
  · exact row3282_q7
  · exact row3282_q8
  · exact row3282_q9
private theorem row3282_m0 : resolveAt exactSites 3303 = some (AXTimes4.expected 3303 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_m1 : resolveAt exactSites 3304 = some (AXTimes4.expected 3303 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_m2 : resolveAt exactSites 3305 = some (AXTimes4.expected 3303 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_m3 : resolveAt exactSites 3306 = some (AXTimes4.expected 3303 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_m4 : resolveAt exactSites 3307 = some (AXTimes4.expected 3303 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3282_m5 : resolveAt exactSites 3308 = some (AXTimes4.expected 3303 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3282_m : AXTimes4.Bound exactSites 3303 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3282_m0
  · exact row3282_m1
  · exact row3282_m2
  · exact row3282_m3
  · exact row3282_m4
  · exact row3282_m5
theorem block3282 : AXMacro.Realizes exactSites .cons 3282 3309 :=
  AXMacro.cons_realizes bound3282_u bound3282_q bound3282_m
private theorem row3309_p0 : resolveAt exactSites 3309 = some (AXPushParam.relocate 3284 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p1 : resolveAt exactSites 3310 = some (AXPushParam.relocate 3284 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p2 : resolveAt exactSites 3311 = some (AXPushParam.relocate 3284 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p3 : resolveAt exactSites 3312 = some (AXPushParam.relocate 3284 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p4 : resolveAt exactSites 3313 = some (AXPushParam.relocate 3284 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p5 : resolveAt exactSites 3314 = some (AXPushParam.relocate 3284 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p6 : resolveAt exactSites 3315 = some (AXPushParam.relocate 3284 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p7 : resolveAt exactSites 3316 = some (AXPushParam.relocate 3284 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p8 : resolveAt exactSites 3317 = some (AXPushParam.relocate 3284 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p9 : resolveAt exactSites 3318 = some (AXPushParam.relocate 3284 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p10 : resolveAt exactSites 3319 = some (AXPushParam.relocate 3284 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p11 : resolveAt exactSites 3320 = some (AXPushParam.relocate 3284 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p12 : resolveAt exactSites 3321 = some (AXPushParam.relocate 3284 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p13 : resolveAt exactSites 3322 = some (AXPushParam.relocate 3284 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p14 : resolveAt exactSites 3323 = some (AXPushParam.relocate 3284 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p15 : resolveAt exactSites 3324 = some (AXPushParam.relocate 3284 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p16 : resolveAt exactSites 3325 = some (AXPushParam.relocate 3284 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p17 : resolveAt exactSites 3326 = some (AXPushParam.relocate 3284 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3309_p18 : resolveAt exactSites 3327 = some (AXPushParam.relocate 3284 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3309_p : AXPushParam.Bound exactSites 3284 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3309_p0
  · exact row3309_p1
  · exact row3309_p2
  · exact row3309_p3
  · exact row3309_p4
  · exact row3309_p5
  · exact row3309_p6
  · exact row3309_p7
  · exact row3309_p8
  · exact row3309_p9
  · exact row3309_p10
  · exact row3309_p11
  · exact row3309_p12
  · exact row3309_p13
  · exact row3309_p14
  · exact row3309_p15
  · exact row3309_p16
  · exact row3309_p17
  · exact row3309_p18
theorem block3309 : AXMacro.Realizes exactSites .push 3309 3328 :=
  AXMacro.push_realizes bound3309_p
private theorem row3328_i0 : resolveAt exactSites 3328 = some (Instruction.inc 1 (some 3329)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block3328 : AXMacro.Realizes exactSites .incT 3328 3329 :=
  AXMacro.inc_realizes row3328_i0
private theorem row3329_u0 : resolveAt exactSites 3329 = some (UnpairPartial.expected 3329 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_u1 : resolveAt exactSites 3330 = some (UnpairPartial.expected 3329 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_u2 : resolveAt exactSites 3331 = some (UnpairPartial.expected 3329 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_u3 : resolveAt exactSites 3332 = some (UnpairPartial.expected 3329 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_u4 : resolveAt exactSites 3333 = some (UnpairPartial.expected 3329 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_u5 : resolveAt exactSites 3334 = some (UnpairPartial.expected 3329 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_u6 : resolveAt exactSites 3335 = some (UnpairPartial.expected 3329 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_u7 : resolveAt exactSites 3336 = some (UnpairPartial.expected 3329 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_u8 : resolveAt exactSites 3337 = some (UnpairPartial.expected 3329 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_u9 : resolveAt exactSites 3338 = some (UnpairPartial.expected 3329 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_u10 : resolveAt exactSites 3339 = some (UnpairPartial.expected 3329 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3329_u : UnpairPartial.Bound exactSites 3329 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3329_u0
  · exact row3329_u1
  · exact row3329_u2
  · exact row3329_u3
  · exact row3329_u4
  · exact row3329_u5
  · exact row3329_u6
  · exact row3329_u7
  · exact row3329_u8
  · exact row3329_u9
  · exact row3329_u10
private theorem row3329_q0 : resolveAt exactSites 3340 = some (AXPair.relocate 3309 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_q1 : resolveAt exactSites 3341 = some (AXPair.relocate 3309 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_q2 : resolveAt exactSites 3342 = some (AXPair.relocate 3309 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_q3 : resolveAt exactSites 3343 = some (AXPair.relocate 3309 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_q4 : resolveAt exactSites 3344 = some (AXPair.relocate 3309 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_q5 : resolveAt exactSites 3345 = some (AXPair.relocate 3309 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_q6 : resolveAt exactSites 3346 = some (AXPair.relocate 3309 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_q7 : resolveAt exactSites 3347 = some (AXPair.relocate 3309 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_q8 : resolveAt exactSites 3348 = some (AXPair.relocate 3309 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_q9 : resolveAt exactSites 3349 = some (AXPair.relocate 3309 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3329_q : AXPair.Bound exactSites 3309 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3329_q0
  · exact row3329_q1
  · exact row3329_q2
  · exact row3329_q3
  · exact row3329_q4
  · exact row3329_q5
  · exact row3329_q6
  · exact row3329_q7
  · exact row3329_q8
  · exact row3329_q9
private theorem row3329_m0 : resolveAt exactSites 3350 = some (AXTimes4.expected 3350 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_m1 : resolveAt exactSites 3351 = some (AXTimes4.expected 3350 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_m2 : resolveAt exactSites 3352 = some (AXTimes4.expected 3350 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_m3 : resolveAt exactSites 3353 = some (AXTimes4.expected 3350 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_m4 : resolveAt exactSites 3354 = some (AXTimes4.expected 3350 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3329_m5 : resolveAt exactSites 3355 = some (AXTimes4.expected 3350 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3329_m : AXTimes4.Bound exactSites 3350 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3329_m0
  · exact row3329_m1
  · exact row3329_m2
  · exact row3329_m3
  · exact row3329_m4
  · exact row3329_m5
theorem block3329 : AXMacro.Realizes exactSites .cons 3329 3356 :=
  AXMacro.cons_realizes bound3329_u bound3329_q bound3329_m
private theorem row3356_u0 : resolveAt exactSites 3356 = some (UnpairPartial.expected 3356 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_u1 : resolveAt exactSites 3357 = some (UnpairPartial.expected 3356 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_u2 : resolveAt exactSites 3358 = some (UnpairPartial.expected 3356 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_u3 : resolveAt exactSites 3359 = some (UnpairPartial.expected 3356 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_u4 : resolveAt exactSites 3360 = some (UnpairPartial.expected 3356 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_u5 : resolveAt exactSites 3361 = some (UnpairPartial.expected 3356 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_u6 : resolveAt exactSites 3362 = some (UnpairPartial.expected 3356 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_u7 : resolveAt exactSites 3363 = some (UnpairPartial.expected 3356 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_u8 : resolveAt exactSites 3364 = some (UnpairPartial.expected 3356 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_u9 : resolveAt exactSites 3365 = some (UnpairPartial.expected 3356 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_u10 : resolveAt exactSites 3366 = some (UnpairPartial.expected 3356 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3356_u : UnpairPartial.Bound exactSites 3356 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3356_u0
  · exact row3356_u1
  · exact row3356_u2
  · exact row3356_u3
  · exact row3356_u4
  · exact row3356_u5
  · exact row3356_u6
  · exact row3356_u7
  · exact row3356_u8
  · exact row3356_u9
  · exact row3356_u10
private theorem row3356_q0 : resolveAt exactSites 3367 = some (AXPair.relocate 3336 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_q1 : resolveAt exactSites 3368 = some (AXPair.relocate 3336 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_q2 : resolveAt exactSites 3369 = some (AXPair.relocate 3336 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_q3 : resolveAt exactSites 3370 = some (AXPair.relocate 3336 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_q4 : resolveAt exactSites 3371 = some (AXPair.relocate 3336 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_q5 : resolveAt exactSites 3372 = some (AXPair.relocate 3336 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_q6 : resolveAt exactSites 3373 = some (AXPair.relocate 3336 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_q7 : resolveAt exactSites 3374 = some (AXPair.relocate 3336 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_q8 : resolveAt exactSites 3375 = some (AXPair.relocate 3336 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_q9 : resolveAt exactSites 3376 = some (AXPair.relocate 3336 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3356_q : AXPair.Bound exactSites 3336 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3356_q0
  · exact row3356_q1
  · exact row3356_q2
  · exact row3356_q3
  · exact row3356_q4
  · exact row3356_q5
  · exact row3356_q6
  · exact row3356_q7
  · exact row3356_q8
  · exact row3356_q9
private theorem row3356_m0 : resolveAt exactSites 3377 = some (AXTimes4.expected 3377 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_m1 : resolveAt exactSites 3378 = some (AXTimes4.expected 3377 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_m2 : resolveAt exactSites 3379 = some (AXTimes4.expected 3377 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_m3 : resolveAt exactSites 3380 = some (AXTimes4.expected 3377 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_m4 : resolveAt exactSites 3381 = some (AXTimes4.expected 3377 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3356_m5 : resolveAt exactSites 3382 = some (AXTimes4.expected 3377 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3356_m : AXTimes4.Bound exactSites 3377 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3356_m0
  · exact row3356_m1
  · exact row3356_m2
  · exact row3356_m3
  · exact row3356_m4
  · exact row3356_m5
theorem block3356 : AXMacro.Realizes exactSites .cons 3356 3383 :=
  AXMacro.cons_realizes bound3356_u bound3356_q bound3356_m
private theorem row3383_p0 : resolveAt exactSites 3383 = some (AXPushParam.relocate 3358 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p1 : resolveAt exactSites 3384 = some (AXPushParam.relocate 3358 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p2 : resolveAt exactSites 3385 = some (AXPushParam.relocate 3358 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p3 : resolveAt exactSites 3386 = some (AXPushParam.relocate 3358 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p4 : resolveAt exactSites 3387 = some (AXPushParam.relocate 3358 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p5 : resolveAt exactSites 3388 = some (AXPushParam.relocate 3358 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p6 : resolveAt exactSites 3389 = some (AXPushParam.relocate 3358 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p7 : resolveAt exactSites 3390 = some (AXPushParam.relocate 3358 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p8 : resolveAt exactSites 3391 = some (AXPushParam.relocate 3358 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p9 : resolveAt exactSites 3392 = some (AXPushParam.relocate 3358 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p10 : resolveAt exactSites 3393 = some (AXPushParam.relocate 3358 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p11 : resolveAt exactSites 3394 = some (AXPushParam.relocate 3358 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p12 : resolveAt exactSites 3395 = some (AXPushParam.relocate 3358 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p13 : resolveAt exactSites 3396 = some (AXPushParam.relocate 3358 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p14 : resolveAt exactSites 3397 = some (AXPushParam.relocate 3358 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p15 : resolveAt exactSites 3398 = some (AXPushParam.relocate 3358 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p16 : resolveAt exactSites 3399 = some (AXPushParam.relocate 3358 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p17 : resolveAt exactSites 3400 = some (AXPushParam.relocate 3358 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row3383_p18 : resolveAt exactSites 3401 = some (AXPushParam.relocate 3358 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound3383_p : AXPushParam.Bound exactSites 3358 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3383_p0
  · exact row3383_p1
  · exact row3383_p2
  · exact row3383_p3
  · exact row3383_p4
  · exact row3383_p5
  · exact row3383_p6
  · exact row3383_p7
  · exact row3383_p8
  · exact row3383_p9
  · exact row3383_p10
  · exact row3383_p11
  · exact row3383_p12
  · exact row3383_p13
  · exact row3383_p14
  · exact row3383_p15
  · exact row3383_p16
  · exact row3383_p17
  · exact row3383_p18
theorem block3383 : AXMacro.Realizes exactSites .push 3383 3402 :=
  AXMacro.push_realizes bound3383_p
private theorem row3402_i0 : resolveAt exactSites 3402 = some (Instruction.inc 1 (some 3403)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block3402 : AXMacro.Realizes exactSites .incT 3402 3403 :=
  AXMacro.inc_realizes row3402_i0
def code020 : List AXMacro.Op := [.copyH,.cons,.incT,.push,.copyA,.cons,.push,.incT,.cons,.cons,.push,.incT]
theorem plan020 : AXMacro.Plan exactSites 3221 3403 code020 :=
  AXMacro.Plan.cons block3221 ( AXMacro.Plan.cons block3228 ( AXMacro.Plan.cons block3255 ( AXMacro.Plan.cons block3256 ( AXMacro.Plan.cons block3275 ( AXMacro.Plan.cons block3282 ( AXMacro.Plan.cons block3309 ( AXMacro.Plan.cons block3328 ( AXMacro.Plan.cons block3329 ( AXMacro.Plan.cons block3356 ( AXMacro.Plan.cons block3383 ( AXMacro.Plan.cons block3402 ( AXMacro.Plan.nil 3403))))))))))))
#print axioms plan020
end M6.Source.AXAll

