module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row2247_u0 : resolveAt exactSites 2247 = some (UnpairPartial.expected 2247 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_u1 : resolveAt exactSites 2248 = some (UnpairPartial.expected 2247 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_u2 : resolveAt exactSites 2249 = some (UnpairPartial.expected 2247 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_u3 : resolveAt exactSites 2250 = some (UnpairPartial.expected 2247 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_u4 : resolveAt exactSites 2251 = some (UnpairPartial.expected 2247 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_u5 : resolveAt exactSites 2252 = some (UnpairPartial.expected 2247 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_u6 : resolveAt exactSites 2253 = some (UnpairPartial.expected 2247 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_u7 : resolveAt exactSites 2254 = some (UnpairPartial.expected 2247 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_u8 : resolveAt exactSites 2255 = some (UnpairPartial.expected 2247 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_u9 : resolveAt exactSites 2256 = some (UnpairPartial.expected 2247 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_u10 : resolveAt exactSites 2257 = some (UnpairPartial.expected 2247 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2247_u : UnpairPartial.Bound exactSites 2247 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2247_u0
  · exact row2247_u1
  · exact row2247_u2
  · exact row2247_u3
  · exact row2247_u4
  · exact row2247_u5
  · exact row2247_u6
  · exact row2247_u7
  · exact row2247_u8
  · exact row2247_u9
  · exact row2247_u10
private theorem row2247_q0 : resolveAt exactSites 2258 = some (AXPair.relocate 2227 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_q1 : resolveAt exactSites 2259 = some (AXPair.relocate 2227 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_q2 : resolveAt exactSites 2260 = some (AXPair.relocate 2227 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_q3 : resolveAt exactSites 2261 = some (AXPair.relocate 2227 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_q4 : resolveAt exactSites 2262 = some (AXPair.relocate 2227 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_q5 : resolveAt exactSites 2263 = some (AXPair.relocate 2227 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_q6 : resolveAt exactSites 2264 = some (AXPair.relocate 2227 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_q7 : resolveAt exactSites 2265 = some (AXPair.relocate 2227 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_q8 : resolveAt exactSites 2266 = some (AXPair.relocate 2227 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_q9 : resolveAt exactSites 2267 = some (AXPair.relocate 2227 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2247_q : AXPair.Bound exactSites 2227 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2247_q0
  · exact row2247_q1
  · exact row2247_q2
  · exact row2247_q3
  · exact row2247_q4
  · exact row2247_q5
  · exact row2247_q6
  · exact row2247_q7
  · exact row2247_q8
  · exact row2247_q9
private theorem row2247_m0 : resolveAt exactSites 2268 = some (AXTimes4.expected 2268 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_m1 : resolveAt exactSites 2269 = some (AXTimes4.expected 2268 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_m2 : resolveAt exactSites 2270 = some (AXTimes4.expected 2268 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_m3 : resolveAt exactSites 2271 = some (AXTimes4.expected 2268 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_m4 : resolveAt exactSites 2272 = some (AXTimes4.expected 2268 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2247_m5 : resolveAt exactSites 2273 = some (AXTimes4.expected 2268 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2247_m : AXTimes4.Bound exactSites 2268 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2247_m0
  · exact row2247_m1
  · exact row2247_m2
  · exact row2247_m3
  · exact row2247_m4
  · exact row2247_m5
theorem block2247 : AXMacro.Realizes exactSites .cons 2247 2274 :=
  AXMacro.cons_realizes bound2247_u bound2247_q bound2247_m
private theorem row2274_i0 : resolveAt exactSites 2274 = some (Instruction.inc 1 (some 2275)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block2274 : AXMacro.Realizes exactSites .incT 2274 2275 :=
  AXMacro.inc_realizes row2274_i0
private theorem row2275_i0 : resolveAt exactSites 2275 = some (Instruction.inc 1 (some 2276)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block2275 : AXMacro.Realizes exactSites .incT 2275 2276 :=
  AXMacro.inc_realizes row2275_i0
private theorem row2276_p0 : resolveAt exactSites 2276 = some (AXPushParam.relocate 2251 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p1 : resolveAt exactSites 2277 = some (AXPushParam.relocate 2251 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p2 : resolveAt exactSites 2278 = some (AXPushParam.relocate 2251 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p3 : resolveAt exactSites 2279 = some (AXPushParam.relocate 2251 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p4 : resolveAt exactSites 2280 = some (AXPushParam.relocate 2251 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p5 : resolveAt exactSites 2281 = some (AXPushParam.relocate 2251 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p6 : resolveAt exactSites 2282 = some (AXPushParam.relocate 2251 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p7 : resolveAt exactSites 2283 = some (AXPushParam.relocate 2251 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p8 : resolveAt exactSites 2284 = some (AXPushParam.relocate 2251 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p9 : resolveAt exactSites 2285 = some (AXPushParam.relocate 2251 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p10 : resolveAt exactSites 2286 = some (AXPushParam.relocate 2251 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p11 : resolveAt exactSites 2287 = some (AXPushParam.relocate 2251 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p12 : resolveAt exactSites 2288 = some (AXPushParam.relocate 2251 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p13 : resolveAt exactSites 2289 = some (AXPushParam.relocate 2251 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p14 : resolveAt exactSites 2290 = some (AXPushParam.relocate 2251 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p15 : resolveAt exactSites 2291 = some (AXPushParam.relocate 2251 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p16 : resolveAt exactSites 2292 = some (AXPushParam.relocate 2251 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p17 : resolveAt exactSites 2293 = some (AXPushParam.relocate 2251 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2276_p18 : resolveAt exactSites 2294 = some (AXPushParam.relocate 2251 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2276_p : AXPushParam.Bound exactSites 2251 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2276_p0
  · exact row2276_p1
  · exact row2276_p2
  · exact row2276_p3
  · exact row2276_p4
  · exact row2276_p5
  · exact row2276_p6
  · exact row2276_p7
  · exact row2276_p8
  · exact row2276_p9
  · exact row2276_p10
  · exact row2276_p11
  · exact row2276_p12
  · exact row2276_p13
  · exact row2276_p14
  · exact row2276_p15
  · exact row2276_p16
  · exact row2276_p17
  · exact row2276_p18
theorem block2276 : AXMacro.Realizes exactSites .push 2276 2295 :=
  AXMacro.push_realizes bound2276_p
private theorem row2295_c0 : resolveAt exactSites 2295 = some (CopyToT.expected 4 2295 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2295_c1 : resolveAt exactSites 2296 = some (CopyToT.expected 4 2295 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2295_c2 : resolveAt exactSites 2297 = some (CopyToT.expected 4 2295 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2295_c3 : resolveAt exactSites 2298 = some (CopyToT.expected 4 2295 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2295_c4 : resolveAt exactSites 2299 = some (CopyToT.expected 4 2295 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2295_c5 : resolveAt exactSites 2300 = some (CopyToT.expected 4 2295 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2295_c6 : resolveAt exactSites 2301 = some (CopyToT.expected 4 2295 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2295_c : CopyToT.Bound exactSites 4 2295 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2295_c0
  · exact row2295_c1
  · exact row2295_c2
  · exact row2295_c3
  · exact row2295_c4
  · exact row2295_c5
  · exact row2295_c6
theorem block2295 : AXMacro.Realizes exactSites .copyD 2295 2302 :=
  AXMacro.copyD_realizes bound2295_c
private theorem row2302_p0 : resolveAt exactSites 2302 = some (AXPushParam.relocate 2277 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p1 : resolveAt exactSites 2303 = some (AXPushParam.relocate 2277 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p2 : resolveAt exactSites 2304 = some (AXPushParam.relocate 2277 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p3 : resolveAt exactSites 2305 = some (AXPushParam.relocate 2277 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p4 : resolveAt exactSites 2306 = some (AXPushParam.relocate 2277 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p5 : resolveAt exactSites 2307 = some (AXPushParam.relocate 2277 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p6 : resolveAt exactSites 2308 = some (AXPushParam.relocate 2277 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p7 : resolveAt exactSites 2309 = some (AXPushParam.relocate 2277 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p8 : resolveAt exactSites 2310 = some (AXPushParam.relocate 2277 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p9 : resolveAt exactSites 2311 = some (AXPushParam.relocate 2277 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p10 : resolveAt exactSites 2312 = some (AXPushParam.relocate 2277 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p11 : resolveAt exactSites 2313 = some (AXPushParam.relocate 2277 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p12 : resolveAt exactSites 2314 = some (AXPushParam.relocate 2277 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p13 : resolveAt exactSites 2315 = some (AXPushParam.relocate 2277 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p14 : resolveAt exactSites 2316 = some (AXPushParam.relocate 2277 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p15 : resolveAt exactSites 2317 = some (AXPushParam.relocate 2277 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p16 : resolveAt exactSites 2318 = some (AXPushParam.relocate 2277 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p17 : resolveAt exactSites 2319 = some (AXPushParam.relocate 2277 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2302_p18 : resolveAt exactSites 2320 = some (AXPushParam.relocate 2277 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2302_p : AXPushParam.Bound exactSites 2277 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2302_p0
  · exact row2302_p1
  · exact row2302_p2
  · exact row2302_p3
  · exact row2302_p4
  · exact row2302_p5
  · exact row2302_p6
  · exact row2302_p7
  · exact row2302_p8
  · exact row2302_p9
  · exact row2302_p10
  · exact row2302_p11
  · exact row2302_p12
  · exact row2302_p13
  · exact row2302_p14
  · exact row2302_p15
  · exact row2302_p16
  · exact row2302_p17
  · exact row2302_p18
theorem block2302 : AXMacro.Realizes exactSites .push 2302 2321 :=
  AXMacro.push_realizes bound2302_p
private theorem row2321_c0 : resolveAt exactSites 2321 = some (CopyToT.expected 3 2321 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2321_c1 : resolveAt exactSites 2322 = some (CopyToT.expected 3 2321 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2321_c2 : resolveAt exactSites 2323 = some (CopyToT.expected 3 2321 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2321_c3 : resolveAt exactSites 2324 = some (CopyToT.expected 3 2321 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2321_c4 : resolveAt exactSites 2325 = some (CopyToT.expected 3 2321 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2321_c5 : resolveAt exactSites 2326 = some (CopyToT.expected 3 2321 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2321_c6 : resolveAt exactSites 2327 = some (CopyToT.expected 3 2321 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2321_c : CopyToT.Bound exactSites 3 2321 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2321_c0
  · exact row2321_c1
  · exact row2321_c2
  · exact row2321_c3
  · exact row2321_c4
  · exact row2321_c5
  · exact row2321_c6
theorem block2321 : AXMacro.Realizes exactSites .copyA 2321 2328 :=
  AXMacro.copyA_realizes bound2321_c
private theorem row2328_u0 : resolveAt exactSites 2328 = some (UnpairPartial.expected 2328 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_u1 : resolveAt exactSites 2329 = some (UnpairPartial.expected 2328 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_u2 : resolveAt exactSites 2330 = some (UnpairPartial.expected 2328 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_u3 : resolveAt exactSites 2331 = some (UnpairPartial.expected 2328 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_u4 : resolveAt exactSites 2332 = some (UnpairPartial.expected 2328 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_u5 : resolveAt exactSites 2333 = some (UnpairPartial.expected 2328 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_u6 : resolveAt exactSites 2334 = some (UnpairPartial.expected 2328 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_u7 : resolveAt exactSites 2335 = some (UnpairPartial.expected 2328 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_u8 : resolveAt exactSites 2336 = some (UnpairPartial.expected 2328 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_u9 : resolveAt exactSites 2337 = some (UnpairPartial.expected 2328 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_u10 : resolveAt exactSites 2338 = some (UnpairPartial.expected 2328 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2328_u : UnpairPartial.Bound exactSites 2328 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2328_u0
  · exact row2328_u1
  · exact row2328_u2
  · exact row2328_u3
  · exact row2328_u4
  · exact row2328_u5
  · exact row2328_u6
  · exact row2328_u7
  · exact row2328_u8
  · exact row2328_u9
  · exact row2328_u10
private theorem row2328_q0 : resolveAt exactSites 2339 = some (AXPair.relocate 2308 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_q1 : resolveAt exactSites 2340 = some (AXPair.relocate 2308 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_q2 : resolveAt exactSites 2341 = some (AXPair.relocate 2308 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_q3 : resolveAt exactSites 2342 = some (AXPair.relocate 2308 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_q4 : resolveAt exactSites 2343 = some (AXPair.relocate 2308 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_q5 : resolveAt exactSites 2344 = some (AXPair.relocate 2308 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_q6 : resolveAt exactSites 2345 = some (AXPair.relocate 2308 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_q7 : resolveAt exactSites 2346 = some (AXPair.relocate 2308 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_q8 : resolveAt exactSites 2347 = some (AXPair.relocate 2308 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_q9 : resolveAt exactSites 2348 = some (AXPair.relocate 2308 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2328_q : AXPair.Bound exactSites 2308 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2328_q0
  · exact row2328_q1
  · exact row2328_q2
  · exact row2328_q3
  · exact row2328_q4
  · exact row2328_q5
  · exact row2328_q6
  · exact row2328_q7
  · exact row2328_q8
  · exact row2328_q9
private theorem row2328_m0 : resolveAt exactSites 2349 = some (AXTimes4.expected 2349 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_m1 : resolveAt exactSites 2350 = some (AXTimes4.expected 2349 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_m2 : resolveAt exactSites 2351 = some (AXTimes4.expected 2349 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_m3 : resolveAt exactSites 2352 = some (AXTimes4.expected 2349 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_m4 : resolveAt exactSites 2353 = some (AXTimes4.expected 2349 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2328_m5 : resolveAt exactSites 2354 = some (AXTimes4.expected 2349 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2328_m : AXTimes4.Bound exactSites 2349 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2328_m0
  · exact row2328_m1
  · exact row2328_m2
  · exact row2328_m3
  · exact row2328_m4
  · exact row2328_m5
theorem block2328 : AXMacro.Realizes exactSites .cons 2328 2355 :=
  AXMacro.cons_realizes bound2328_u bound2328_q bound2328_m
private theorem row2355_i0 : resolveAt exactSites 2355 = some (Instruction.inc 1 (some 2356)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block2355 : AXMacro.Realizes exactSites .incT 2355 2356 :=
  AXMacro.inc_realizes row2355_i0
private theorem row2356_i0 : resolveAt exactSites 2356 = some (Instruction.inc 1 (some 2357)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block2356 : AXMacro.Realizes exactSites .incT 2356 2357 :=
  AXMacro.inc_realizes row2356_i0
private theorem row2357_u0 : resolveAt exactSites 2357 = some (UnpairPartial.expected 2357 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_u1 : resolveAt exactSites 2358 = some (UnpairPartial.expected 2357 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_u2 : resolveAt exactSites 2359 = some (UnpairPartial.expected 2357 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_u3 : resolveAt exactSites 2360 = some (UnpairPartial.expected 2357 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_u4 : resolveAt exactSites 2361 = some (UnpairPartial.expected 2357 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_u5 : resolveAt exactSites 2362 = some (UnpairPartial.expected 2357 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_u6 : resolveAt exactSites 2363 = some (UnpairPartial.expected 2357 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_u7 : resolveAt exactSites 2364 = some (UnpairPartial.expected 2357 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_u8 : resolveAt exactSites 2365 = some (UnpairPartial.expected 2357 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_u9 : resolveAt exactSites 2366 = some (UnpairPartial.expected 2357 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_u10 : resolveAt exactSites 2367 = some (UnpairPartial.expected 2357 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2357_u : UnpairPartial.Bound exactSites 2357 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2357_u0
  · exact row2357_u1
  · exact row2357_u2
  · exact row2357_u3
  · exact row2357_u4
  · exact row2357_u5
  · exact row2357_u6
  · exact row2357_u7
  · exact row2357_u8
  · exact row2357_u9
  · exact row2357_u10
private theorem row2357_q0 : resolveAt exactSites 2368 = some (AXPair.relocate 2337 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_q1 : resolveAt exactSites 2369 = some (AXPair.relocate 2337 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_q2 : resolveAt exactSites 2370 = some (AXPair.relocate 2337 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_q3 : resolveAt exactSites 2371 = some (AXPair.relocate 2337 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_q4 : resolveAt exactSites 2372 = some (AXPair.relocate 2337 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_q5 : resolveAt exactSites 2373 = some (AXPair.relocate 2337 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_q6 : resolveAt exactSites 2374 = some (AXPair.relocate 2337 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_q7 : resolveAt exactSites 2375 = some (AXPair.relocate 2337 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_q8 : resolveAt exactSites 2376 = some (AXPair.relocate 2337 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_q9 : resolveAt exactSites 2377 = some (AXPair.relocate 2337 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2357_q : AXPair.Bound exactSites 2337 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2357_q0
  · exact row2357_q1
  · exact row2357_q2
  · exact row2357_q3
  · exact row2357_q4
  · exact row2357_q5
  · exact row2357_q6
  · exact row2357_q7
  · exact row2357_q8
  · exact row2357_q9
private theorem row2357_m0 : resolveAt exactSites 2378 = some (AXTimes4.expected 2378 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_m1 : resolveAt exactSites 2379 = some (AXTimes4.expected 2378 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_m2 : resolveAt exactSites 2380 = some (AXTimes4.expected 2378 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_m3 : resolveAt exactSites 2381 = some (AXTimes4.expected 2378 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_m4 : resolveAt exactSites 2382 = some (AXTimes4.expected 2378 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2357_m5 : resolveAt exactSites 2383 = some (AXTimes4.expected 2378 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2357_m : AXTimes4.Bound exactSites 2378 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2357_m0
  · exact row2357_m1
  · exact row2357_m2
  · exact row2357_m3
  · exact row2357_m4
  · exact row2357_m5
theorem block2357 : AXMacro.Realizes exactSites .cons 2357 2384 :=
  AXMacro.cons_realizes bound2357_u bound2357_q bound2357_m
private theorem row2384_u0 : resolveAt exactSites 2384 = some (UnpairPartial.expected 2384 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_u1 : resolveAt exactSites 2385 = some (UnpairPartial.expected 2384 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_u2 : resolveAt exactSites 2386 = some (UnpairPartial.expected 2384 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_u3 : resolveAt exactSites 2387 = some (UnpairPartial.expected 2384 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_u4 : resolveAt exactSites 2388 = some (UnpairPartial.expected 2384 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_u5 : resolveAt exactSites 2389 = some (UnpairPartial.expected 2384 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_u6 : resolveAt exactSites 2390 = some (UnpairPartial.expected 2384 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_u7 : resolveAt exactSites 2391 = some (UnpairPartial.expected 2384 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_u8 : resolveAt exactSites 2392 = some (UnpairPartial.expected 2384 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_u9 : resolveAt exactSites 2393 = some (UnpairPartial.expected 2384 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_u10 : resolveAt exactSites 2394 = some (UnpairPartial.expected 2384 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2384_u : UnpairPartial.Bound exactSites 2384 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2384_u0
  · exact row2384_u1
  · exact row2384_u2
  · exact row2384_u3
  · exact row2384_u4
  · exact row2384_u5
  · exact row2384_u6
  · exact row2384_u7
  · exact row2384_u8
  · exact row2384_u9
  · exact row2384_u10
private theorem row2384_q0 : resolveAt exactSites 2395 = some (AXPair.relocate 2364 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_q1 : resolveAt exactSites 2396 = some (AXPair.relocate 2364 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_q2 : resolveAt exactSites 2397 = some (AXPair.relocate 2364 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_q3 : resolveAt exactSites 2398 = some (AXPair.relocate 2364 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_q4 : resolveAt exactSites 2399 = some (AXPair.relocate 2364 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_q5 : resolveAt exactSites 2400 = some (AXPair.relocate 2364 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_q6 : resolveAt exactSites 2401 = some (AXPair.relocate 2364 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_q7 : resolveAt exactSites 2402 = some (AXPair.relocate 2364 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_q8 : resolveAt exactSites 2403 = some (AXPair.relocate 2364 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_q9 : resolveAt exactSites 2404 = some (AXPair.relocate 2364 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2384_q : AXPair.Bound exactSites 2364 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2384_q0
  · exact row2384_q1
  · exact row2384_q2
  · exact row2384_q3
  · exact row2384_q4
  · exact row2384_q5
  · exact row2384_q6
  · exact row2384_q7
  · exact row2384_q8
  · exact row2384_q9
private theorem row2384_m0 : resolveAt exactSites 2405 = some (AXTimes4.expected 2405 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_m1 : resolveAt exactSites 2406 = some (AXTimes4.expected 2405 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_m2 : resolveAt exactSites 2407 = some (AXTimes4.expected 2405 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_m3 : resolveAt exactSites 2408 = some (AXTimes4.expected 2405 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_m4 : resolveAt exactSites 2409 = some (AXTimes4.expected 2405 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2384_m5 : resolveAt exactSites 2410 = some (AXTimes4.expected 2405 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2384_m : AXTimes4.Bound exactSites 2405 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2384_m0
  · exact row2384_m1
  · exact row2384_m2
  · exact row2384_m3
  · exact row2384_m4
  · exact row2384_m5
theorem block2384 : AXMacro.Realizes exactSites .cons 2384 2411 :=
  AXMacro.cons_realizes bound2384_u bound2384_q bound2384_m
def code014 : List AXMacro.Op := [.cons,.incT,.incT,.push,.copyD,.push,.copyA,.cons,.incT,.incT,.cons,.cons]
theorem plan014 : AXMacro.Plan exactSites 2247 2411 code014 :=
  AXMacro.Plan.cons block2247 ( AXMacro.Plan.cons block2274 ( AXMacro.Plan.cons block2275 ( AXMacro.Plan.cons block2276 ( AXMacro.Plan.cons block2295 ( AXMacro.Plan.cons block2302 ( AXMacro.Plan.cons block2321 ( AXMacro.Plan.cons block2328 ( AXMacro.Plan.cons block2355 ( AXMacro.Plan.cons block2356 ( AXMacro.Plan.cons block2357 ( AXMacro.Plan.cons block2384 ( AXMacro.Plan.nil 2411))))))))))))
#print axioms plan014
end M6.Source.AXAll

