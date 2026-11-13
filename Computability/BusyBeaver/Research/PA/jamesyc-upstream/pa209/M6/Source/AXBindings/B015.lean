module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row2411_p0 : resolveAt exactSites 2411 = some (AXPushParam.relocate 2386 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p1 : resolveAt exactSites 2412 = some (AXPushParam.relocate 2386 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p2 : resolveAt exactSites 2413 = some (AXPushParam.relocate 2386 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p3 : resolveAt exactSites 2414 = some (AXPushParam.relocate 2386 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p4 : resolveAt exactSites 2415 = some (AXPushParam.relocate 2386 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p5 : resolveAt exactSites 2416 = some (AXPushParam.relocate 2386 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p6 : resolveAt exactSites 2417 = some (AXPushParam.relocate 2386 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p7 : resolveAt exactSites 2418 = some (AXPushParam.relocate 2386 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p8 : resolveAt exactSites 2419 = some (AXPushParam.relocate 2386 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p9 : resolveAt exactSites 2420 = some (AXPushParam.relocate 2386 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p10 : resolveAt exactSites 2421 = some (AXPushParam.relocate 2386 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p11 : resolveAt exactSites 2422 = some (AXPushParam.relocate 2386 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p12 : resolveAt exactSites 2423 = some (AXPushParam.relocate 2386 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p13 : resolveAt exactSites 2424 = some (AXPushParam.relocate 2386 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p14 : resolveAt exactSites 2425 = some (AXPushParam.relocate 2386 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p15 : resolveAt exactSites 2426 = some (AXPushParam.relocate 2386 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p16 : resolveAt exactSites 2427 = some (AXPushParam.relocate 2386 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p17 : resolveAt exactSites 2428 = some (AXPushParam.relocate 2386 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2411_p18 : resolveAt exactSites 2429 = some (AXPushParam.relocate 2386 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2411_p : AXPushParam.Bound exactSites 2386 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2411_p0
  · exact row2411_p1
  · exact row2411_p2
  · exact row2411_p3
  · exact row2411_p4
  · exact row2411_p5
  · exact row2411_p6
  · exact row2411_p7
  · exact row2411_p8
  · exact row2411_p9
  · exact row2411_p10
  · exact row2411_p11
  · exact row2411_p12
  · exact row2411_p13
  · exact row2411_p14
  · exact row2411_p15
  · exact row2411_p16
  · exact row2411_p17
  · exact row2411_p18
theorem block2411 : AXMacro.Realizes exactSites .push 2411 2430 :=
  AXMacro.push_realizes bound2411_p
private theorem row2430_c0 : resolveAt exactSites 2430 = some (CopyToT.expected 4 2430 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2430_c1 : resolveAt exactSites 2431 = some (CopyToT.expected 4 2430 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2430_c2 : resolveAt exactSites 2432 = some (CopyToT.expected 4 2430 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2430_c3 : resolveAt exactSites 2433 = some (CopyToT.expected 4 2430 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2430_c4 : resolveAt exactSites 2434 = some (CopyToT.expected 4 2430 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2430_c5 : resolveAt exactSites 2435 = some (CopyToT.expected 4 2430 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2430_c6 : resolveAt exactSites 2436 = some (CopyToT.expected 4 2430 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2430_c : CopyToT.Bound exactSites 4 2430 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2430_c0
  · exact row2430_c1
  · exact row2430_c2
  · exact row2430_c3
  · exact row2430_c4
  · exact row2430_c5
  · exact row2430_c6
theorem block2430 : AXMacro.Realizes exactSites .copyD 2430 2437 :=
  AXMacro.copyD_realizes bound2430_c
private theorem row2437_p0 : resolveAt exactSites 2437 = some (AXPushParam.relocate 2412 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p1 : resolveAt exactSites 2438 = some (AXPushParam.relocate 2412 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p2 : resolveAt exactSites 2439 = some (AXPushParam.relocate 2412 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p3 : resolveAt exactSites 2440 = some (AXPushParam.relocate 2412 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p4 : resolveAt exactSites 2441 = some (AXPushParam.relocate 2412 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p5 : resolveAt exactSites 2442 = some (AXPushParam.relocate 2412 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p6 : resolveAt exactSites 2443 = some (AXPushParam.relocate 2412 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p7 : resolveAt exactSites 2444 = some (AXPushParam.relocate 2412 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p8 : resolveAt exactSites 2445 = some (AXPushParam.relocate 2412 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p9 : resolveAt exactSites 2446 = some (AXPushParam.relocate 2412 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p10 : resolveAt exactSites 2447 = some (AXPushParam.relocate 2412 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p11 : resolveAt exactSites 2448 = some (AXPushParam.relocate 2412 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p12 : resolveAt exactSites 2449 = some (AXPushParam.relocate 2412 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p13 : resolveAt exactSites 2450 = some (AXPushParam.relocate 2412 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p14 : resolveAt exactSites 2451 = some (AXPushParam.relocate 2412 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p15 : resolveAt exactSites 2452 = some (AXPushParam.relocate 2412 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p16 : resolveAt exactSites 2453 = some (AXPushParam.relocate 2412 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p17 : resolveAt exactSites 2454 = some (AXPushParam.relocate 2412 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2437_p18 : resolveAt exactSites 2455 = some (AXPushParam.relocate 2412 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2437_p : AXPushParam.Bound exactSites 2412 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2437_p0
  · exact row2437_p1
  · exact row2437_p2
  · exact row2437_p3
  · exact row2437_p4
  · exact row2437_p5
  · exact row2437_p6
  · exact row2437_p7
  · exact row2437_p8
  · exact row2437_p9
  · exact row2437_p10
  · exact row2437_p11
  · exact row2437_p12
  · exact row2437_p13
  · exact row2437_p14
  · exact row2437_p15
  · exact row2437_p16
  · exact row2437_p17
  · exact row2437_p18
theorem block2437 : AXMacro.Realizes exactSites .push 2437 2456 :=
  AXMacro.push_realizes bound2437_p
private theorem row2456_c0 : resolveAt exactSites 2456 = some (CopyToT.expected 4 2456 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2456_c1 : resolveAt exactSites 2457 = some (CopyToT.expected 4 2456 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2456_c2 : resolveAt exactSites 2458 = some (CopyToT.expected 4 2456 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2456_c3 : resolveAt exactSites 2459 = some (CopyToT.expected 4 2456 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2456_c4 : resolveAt exactSites 2460 = some (CopyToT.expected 4 2456 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2456_c5 : resolveAt exactSites 2461 = some (CopyToT.expected 4 2456 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2456_c6 : resolveAt exactSites 2462 = some (CopyToT.expected 4 2456 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2456_c : CopyToT.Bound exactSites 4 2456 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2456_c0
  · exact row2456_c1
  · exact row2456_c2
  · exact row2456_c3
  · exact row2456_c4
  · exact row2456_c5
  · exact row2456_c6
theorem block2456 : AXMacro.Realizes exactSites .copyD 2456 2463 :=
  AXMacro.copyD_realizes bound2456_c
private theorem row2463_p0 : resolveAt exactSites 2463 = some (AXPushParam.relocate 2438 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p1 : resolveAt exactSites 2464 = some (AXPushParam.relocate 2438 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p2 : resolveAt exactSites 2465 = some (AXPushParam.relocate 2438 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p3 : resolveAt exactSites 2466 = some (AXPushParam.relocate 2438 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p4 : resolveAt exactSites 2467 = some (AXPushParam.relocate 2438 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p5 : resolveAt exactSites 2468 = some (AXPushParam.relocate 2438 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p6 : resolveAt exactSites 2469 = some (AXPushParam.relocate 2438 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p7 : resolveAt exactSites 2470 = some (AXPushParam.relocate 2438 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p8 : resolveAt exactSites 2471 = some (AXPushParam.relocate 2438 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p9 : resolveAt exactSites 2472 = some (AXPushParam.relocate 2438 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p10 : resolveAt exactSites 2473 = some (AXPushParam.relocate 2438 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p11 : resolveAt exactSites 2474 = some (AXPushParam.relocate 2438 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p12 : resolveAt exactSites 2475 = some (AXPushParam.relocate 2438 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p13 : resolveAt exactSites 2476 = some (AXPushParam.relocate 2438 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p14 : resolveAt exactSites 2477 = some (AXPushParam.relocate 2438 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p15 : resolveAt exactSites 2478 = some (AXPushParam.relocate 2438 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p16 : resolveAt exactSites 2479 = some (AXPushParam.relocate 2438 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p17 : resolveAt exactSites 2480 = some (AXPushParam.relocate 2438 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2463_p18 : resolveAt exactSites 2481 = some (AXPushParam.relocate 2438 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2463_p : AXPushParam.Bound exactSites 2438 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2463_p0
  · exact row2463_p1
  · exact row2463_p2
  · exact row2463_p3
  · exact row2463_p4
  · exact row2463_p5
  · exact row2463_p6
  · exact row2463_p7
  · exact row2463_p8
  · exact row2463_p9
  · exact row2463_p10
  · exact row2463_p11
  · exact row2463_p12
  · exact row2463_p13
  · exact row2463_p14
  · exact row2463_p15
  · exact row2463_p16
  · exact row2463_p17
  · exact row2463_p18
theorem block2463 : AXMacro.Realizes exactSites .push 2463 2482 :=
  AXMacro.push_realizes bound2463_p
private theorem row2482_c0 : resolveAt exactSites 2482 = some (CopyToT.expected 5 2482 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2482_c1 : resolveAt exactSites 2483 = some (CopyToT.expected 5 2482 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2482_c2 : resolveAt exactSites 2484 = some (CopyToT.expected 5 2482 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2482_c3 : resolveAt exactSites 2485 = some (CopyToT.expected 5 2482 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2482_c4 : resolveAt exactSites 2486 = some (CopyToT.expected 5 2482 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2482_c5 : resolveAt exactSites 2487 = some (CopyToT.expected 5 2482 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2482_c6 : resolveAt exactSites 2488 = some (CopyToT.expected 5 2482 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2482_c : CopyToT.Bound exactSites 5 2482 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2482_c0
  · exact row2482_c1
  · exact row2482_c2
  · exact row2482_c3
  · exact row2482_c4
  · exact row2482_c5
  · exact row2482_c6
theorem block2482 : AXMacro.Realizes exactSites .copyH 2482 2489 :=
  AXMacro.copyH_realizes bound2482_c
private theorem row2489_u0 : resolveAt exactSites 2489 = some (UnpairPartial.expected 2489 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_u1 : resolveAt exactSites 2490 = some (UnpairPartial.expected 2489 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_u2 : resolveAt exactSites 2491 = some (UnpairPartial.expected 2489 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_u3 : resolveAt exactSites 2492 = some (UnpairPartial.expected 2489 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_u4 : resolveAt exactSites 2493 = some (UnpairPartial.expected 2489 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_u5 : resolveAt exactSites 2494 = some (UnpairPartial.expected 2489 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_u6 : resolveAt exactSites 2495 = some (UnpairPartial.expected 2489 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_u7 : resolveAt exactSites 2496 = some (UnpairPartial.expected 2489 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_u8 : resolveAt exactSites 2497 = some (UnpairPartial.expected 2489 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_u9 : resolveAt exactSites 2498 = some (UnpairPartial.expected 2489 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_u10 : resolveAt exactSites 2499 = some (UnpairPartial.expected 2489 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2489_u : UnpairPartial.Bound exactSites 2489 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2489_u0
  · exact row2489_u1
  · exact row2489_u2
  · exact row2489_u3
  · exact row2489_u4
  · exact row2489_u5
  · exact row2489_u6
  · exact row2489_u7
  · exact row2489_u8
  · exact row2489_u9
  · exact row2489_u10
private theorem row2489_q0 : resolveAt exactSites 2500 = some (AXPair.relocate 2469 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_q1 : resolveAt exactSites 2501 = some (AXPair.relocate 2469 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_q2 : resolveAt exactSites 2502 = some (AXPair.relocate 2469 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_q3 : resolveAt exactSites 2503 = some (AXPair.relocate 2469 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_q4 : resolveAt exactSites 2504 = some (AXPair.relocate 2469 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_q5 : resolveAt exactSites 2505 = some (AXPair.relocate 2469 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_q6 : resolveAt exactSites 2506 = some (AXPair.relocate 2469 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_q7 : resolveAt exactSites 2507 = some (AXPair.relocate 2469 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_q8 : resolveAt exactSites 2508 = some (AXPair.relocate 2469 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_q9 : resolveAt exactSites 2509 = some (AXPair.relocate 2469 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2489_q : AXPair.Bound exactSites 2469 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2489_q0
  · exact row2489_q1
  · exact row2489_q2
  · exact row2489_q3
  · exact row2489_q4
  · exact row2489_q5
  · exact row2489_q6
  · exact row2489_q7
  · exact row2489_q8
  · exact row2489_q9
private theorem row2489_m0 : resolveAt exactSites 2510 = some (AXTimes4.expected 2510 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_m1 : resolveAt exactSites 2511 = some (AXTimes4.expected 2510 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_m2 : resolveAt exactSites 2512 = some (AXTimes4.expected 2510 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_m3 : resolveAt exactSites 2513 = some (AXTimes4.expected 2510 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_m4 : resolveAt exactSites 2514 = some (AXTimes4.expected 2510 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2489_m5 : resolveAt exactSites 2515 = some (AXTimes4.expected 2510 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2489_m : AXTimes4.Bound exactSites 2510 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2489_m0
  · exact row2489_m1
  · exact row2489_m2
  · exact row2489_m3
  · exact row2489_m4
  · exact row2489_m5
theorem block2489 : AXMacro.Realizes exactSites .cons 2489 2516 :=
  AXMacro.cons_realizes bound2489_u bound2489_q bound2489_m
private theorem row2516_i0 : resolveAt exactSites 2516 = some (Instruction.inc 1 (some 2517)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block2516 : AXMacro.Realizes exactSites .incT 2516 2517 :=
  AXMacro.inc_realizes row2516_i0
private theorem row2517_i0 : resolveAt exactSites 2517 = some (Instruction.inc 1 (some 2518)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block2517 : AXMacro.Realizes exactSites .incT 2517 2518 :=
  AXMacro.inc_realizes row2517_i0
private theorem row2518_i0 : resolveAt exactSites 2518 = some (Instruction.inc 1 (some 2519)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block2518 : AXMacro.Realizes exactSites .incT 2518 2519 :=
  AXMacro.inc_realizes row2518_i0
private theorem row2519_p0 : resolveAt exactSites 2519 = some (AXPushParam.relocate 2494 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p1 : resolveAt exactSites 2520 = some (AXPushParam.relocate 2494 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p2 : resolveAt exactSites 2521 = some (AXPushParam.relocate 2494 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p3 : resolveAt exactSites 2522 = some (AXPushParam.relocate 2494 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p4 : resolveAt exactSites 2523 = some (AXPushParam.relocate 2494 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p5 : resolveAt exactSites 2524 = some (AXPushParam.relocate 2494 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p6 : resolveAt exactSites 2525 = some (AXPushParam.relocate 2494 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p7 : resolveAt exactSites 2526 = some (AXPushParam.relocate 2494 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p8 : resolveAt exactSites 2527 = some (AXPushParam.relocate 2494 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p9 : resolveAt exactSites 2528 = some (AXPushParam.relocate 2494 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p10 : resolveAt exactSites 2529 = some (AXPushParam.relocate 2494 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p11 : resolveAt exactSites 2530 = some (AXPushParam.relocate 2494 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p12 : resolveAt exactSites 2531 = some (AXPushParam.relocate 2494 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p13 : resolveAt exactSites 2532 = some (AXPushParam.relocate 2494 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p14 : resolveAt exactSites 2533 = some (AXPushParam.relocate 2494 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p15 : resolveAt exactSites 2534 = some (AXPushParam.relocate 2494 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p16 : resolveAt exactSites 2535 = some (AXPushParam.relocate 2494 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p17 : resolveAt exactSites 2536 = some (AXPushParam.relocate 2494 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2519_p18 : resolveAt exactSites 2537 = some (AXPushParam.relocate 2494 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2519_p : AXPushParam.Bound exactSites 2494 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2519_p0
  · exact row2519_p1
  · exact row2519_p2
  · exact row2519_p3
  · exact row2519_p4
  · exact row2519_p5
  · exact row2519_p6
  · exact row2519_p7
  · exact row2519_p8
  · exact row2519_p9
  · exact row2519_p10
  · exact row2519_p11
  · exact row2519_p12
  · exact row2519_p13
  · exact row2519_p14
  · exact row2519_p15
  · exact row2519_p16
  · exact row2519_p17
  · exact row2519_p18
theorem block2519 : AXMacro.Realizes exactSites .push 2519 2538 :=
  AXMacro.push_realizes bound2519_p
private theorem row2538_i0 : resolveAt exactSites 2538 = some (Instruction.inc 1 (some 2539)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block2538 : AXMacro.Realizes exactSites .incT 2538 2539 :=
  AXMacro.inc_realizes row2538_i0
def code015 : List AXMacro.Op := [.push,.copyD,.push,.copyD,.push,.copyH,.cons,.incT,.incT,.incT,.push,.incT]
theorem plan015 : AXMacro.Plan exactSites 2411 2539 code015 :=
  AXMacro.Plan.cons block2411 ( AXMacro.Plan.cons block2430 ( AXMacro.Plan.cons block2437 ( AXMacro.Plan.cons block2456 ( AXMacro.Plan.cons block2463 ( AXMacro.Plan.cons block2482 ( AXMacro.Plan.cons block2489 ( AXMacro.Plan.cons block2516 ( AXMacro.Plan.cons block2517 ( AXMacro.Plan.cons block2518 ( AXMacro.Plan.cons block2519 ( AXMacro.Plan.cons block2538 ( AXMacro.Plan.nil 2539))))))))))))
#print axioms plan015
end M6.Source.AXAll

