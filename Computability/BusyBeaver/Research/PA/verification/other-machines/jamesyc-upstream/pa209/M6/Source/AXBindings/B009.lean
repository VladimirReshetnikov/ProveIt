module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row1485_c0 : resolveAt exactSites 1485 = some (CopyToT.expected 4 1485 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1485_c1 : resolveAt exactSites 1486 = some (CopyToT.expected 4 1485 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1485_c2 : resolveAt exactSites 1487 = some (CopyToT.expected 4 1485 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1485_c3 : resolveAt exactSites 1488 = some (CopyToT.expected 4 1485 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1485_c4 : resolveAt exactSites 1489 = some (CopyToT.expected 4 1485 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1485_c5 : resolveAt exactSites 1490 = some (CopyToT.expected 4 1485 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1485_c6 : resolveAt exactSites 1491 = some (CopyToT.expected 4 1485 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1485_c : CopyToT.Bound exactSites 4 1485 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1485_c0
  · exact row1485_c1
  · exact row1485_c2
  · exact row1485_c3
  · exact row1485_c4
  · exact row1485_c5
  · exact row1485_c6
theorem block1485 : AXMacro.Realizes exactSites .copyD 1485 1492 :=
  AXMacro.copyD_realizes bound1485_c
private theorem row1492_p0 : resolveAt exactSites 1492 = some (AXPushParam.relocate 1467 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p1 : resolveAt exactSites 1493 = some (AXPushParam.relocate 1467 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p2 : resolveAt exactSites 1494 = some (AXPushParam.relocate 1467 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p3 : resolveAt exactSites 1495 = some (AXPushParam.relocate 1467 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p4 : resolveAt exactSites 1496 = some (AXPushParam.relocate 1467 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p5 : resolveAt exactSites 1497 = some (AXPushParam.relocate 1467 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p6 : resolveAt exactSites 1498 = some (AXPushParam.relocate 1467 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p7 : resolveAt exactSites 1499 = some (AXPushParam.relocate 1467 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p8 : resolveAt exactSites 1500 = some (AXPushParam.relocate 1467 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p9 : resolveAt exactSites 1501 = some (AXPushParam.relocate 1467 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p10 : resolveAt exactSites 1502 = some (AXPushParam.relocate 1467 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p11 : resolveAt exactSites 1503 = some (AXPushParam.relocate 1467 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p12 : resolveAt exactSites 1504 = some (AXPushParam.relocate 1467 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p13 : resolveAt exactSites 1505 = some (AXPushParam.relocate 1467 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p14 : resolveAt exactSites 1506 = some (AXPushParam.relocate 1467 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p15 : resolveAt exactSites 1507 = some (AXPushParam.relocate 1467 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p16 : resolveAt exactSites 1508 = some (AXPushParam.relocate 1467 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p17 : resolveAt exactSites 1509 = some (AXPushParam.relocate 1467 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1492_p18 : resolveAt exactSites 1510 = some (AXPushParam.relocate 1467 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1492_p : AXPushParam.Bound exactSites 1467 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1492_p0
  · exact row1492_p1
  · exact row1492_p2
  · exact row1492_p3
  · exact row1492_p4
  · exact row1492_p5
  · exact row1492_p6
  · exact row1492_p7
  · exact row1492_p8
  · exact row1492_p9
  · exact row1492_p10
  · exact row1492_p11
  · exact row1492_p12
  · exact row1492_p13
  · exact row1492_p14
  · exact row1492_p15
  · exact row1492_p16
  · exact row1492_p17
  · exact row1492_p18
theorem block1492 : AXMacro.Realizes exactSites .push 1492 1511 :=
  AXMacro.push_realizes bound1492_p
private theorem row1511_c0 : resolveAt exactSites 1511 = some (CopyToT.expected 5 1511 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1511_c1 : resolveAt exactSites 1512 = some (CopyToT.expected 5 1511 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1511_c2 : resolveAt exactSites 1513 = some (CopyToT.expected 5 1511 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1511_c3 : resolveAt exactSites 1514 = some (CopyToT.expected 5 1511 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1511_c4 : resolveAt exactSites 1515 = some (CopyToT.expected 5 1511 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1511_c5 : resolveAt exactSites 1516 = some (CopyToT.expected 5 1511 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1511_c6 : resolveAt exactSites 1517 = some (CopyToT.expected 5 1511 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1511_c : CopyToT.Bound exactSites 5 1511 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1511_c0
  · exact row1511_c1
  · exact row1511_c2
  · exact row1511_c3
  · exact row1511_c4
  · exact row1511_c5
  · exact row1511_c6
theorem block1511 : AXMacro.Realizes exactSites .copyH 1511 1518 :=
  AXMacro.copyH_realizes bound1511_c
private theorem row1518_p0 : resolveAt exactSites 1518 = some (AXPushParam.relocate 1493 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p1 : resolveAt exactSites 1519 = some (AXPushParam.relocate 1493 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p2 : resolveAt exactSites 1520 = some (AXPushParam.relocate 1493 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p3 : resolveAt exactSites 1521 = some (AXPushParam.relocate 1493 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p4 : resolveAt exactSites 1522 = some (AXPushParam.relocate 1493 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p5 : resolveAt exactSites 1523 = some (AXPushParam.relocate 1493 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p6 : resolveAt exactSites 1524 = some (AXPushParam.relocate 1493 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p7 : resolveAt exactSites 1525 = some (AXPushParam.relocate 1493 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p8 : resolveAt exactSites 1526 = some (AXPushParam.relocate 1493 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p9 : resolveAt exactSites 1527 = some (AXPushParam.relocate 1493 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p10 : resolveAt exactSites 1528 = some (AXPushParam.relocate 1493 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p11 : resolveAt exactSites 1529 = some (AXPushParam.relocate 1493 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p12 : resolveAt exactSites 1530 = some (AXPushParam.relocate 1493 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p13 : resolveAt exactSites 1531 = some (AXPushParam.relocate 1493 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p14 : resolveAt exactSites 1532 = some (AXPushParam.relocate 1493 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p15 : resolveAt exactSites 1533 = some (AXPushParam.relocate 1493 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p16 : resolveAt exactSites 1534 = some (AXPushParam.relocate 1493 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p17 : resolveAt exactSites 1535 = some (AXPushParam.relocate 1493 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1518_p18 : resolveAt exactSites 1536 = some (AXPushParam.relocate 1493 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1518_p : AXPushParam.Bound exactSites 1493 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1518_p0
  · exact row1518_p1
  · exact row1518_p2
  · exact row1518_p3
  · exact row1518_p4
  · exact row1518_p5
  · exact row1518_p6
  · exact row1518_p7
  · exact row1518_p8
  · exact row1518_p9
  · exact row1518_p10
  · exact row1518_p11
  · exact row1518_p12
  · exact row1518_p13
  · exact row1518_p14
  · exact row1518_p15
  · exact row1518_p16
  · exact row1518_p17
  · exact row1518_p18
theorem block1518 : AXMacro.Realizes exactSites .push 1518 1537 :=
  AXMacro.push_realizes bound1518_p
private theorem row1537_c0 : resolveAt exactSites 1537 = some (CopyToT.expected 3 1537 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1537_c1 : resolveAt exactSites 1538 = some (CopyToT.expected 3 1537 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1537_c2 : resolveAt exactSites 1539 = some (CopyToT.expected 3 1537 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1537_c3 : resolveAt exactSites 1540 = some (CopyToT.expected 3 1537 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1537_c4 : resolveAt exactSites 1541 = some (CopyToT.expected 3 1537 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1537_c5 : resolveAt exactSites 1542 = some (CopyToT.expected 3 1537 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1537_c6 : resolveAt exactSites 1543 = some (CopyToT.expected 3 1537 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1537_c : CopyToT.Bound exactSites 3 1537 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1537_c0
  · exact row1537_c1
  · exact row1537_c2
  · exact row1537_c3
  · exact row1537_c4
  · exact row1537_c5
  · exact row1537_c6
theorem block1537 : AXMacro.Realizes exactSites .copyA 1537 1544 :=
  AXMacro.copyA_realizes bound1537_c
private theorem row1544_u0 : resolveAt exactSites 1544 = some (UnpairPartial.expected 1544 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_u1 : resolveAt exactSites 1545 = some (UnpairPartial.expected 1544 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_u2 : resolveAt exactSites 1546 = some (UnpairPartial.expected 1544 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_u3 : resolveAt exactSites 1547 = some (UnpairPartial.expected 1544 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_u4 : resolveAt exactSites 1548 = some (UnpairPartial.expected 1544 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_u5 : resolveAt exactSites 1549 = some (UnpairPartial.expected 1544 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_u6 : resolveAt exactSites 1550 = some (UnpairPartial.expected 1544 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_u7 : resolveAt exactSites 1551 = some (UnpairPartial.expected 1544 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_u8 : resolveAt exactSites 1552 = some (UnpairPartial.expected 1544 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_u9 : resolveAt exactSites 1553 = some (UnpairPartial.expected 1544 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_u10 : resolveAt exactSites 1554 = some (UnpairPartial.expected 1544 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1544_u : UnpairPartial.Bound exactSites 1544 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1544_u0
  · exact row1544_u1
  · exact row1544_u2
  · exact row1544_u3
  · exact row1544_u4
  · exact row1544_u5
  · exact row1544_u6
  · exact row1544_u7
  · exact row1544_u8
  · exact row1544_u9
  · exact row1544_u10
private theorem row1544_q0 : resolveAt exactSites 1555 = some (AXPair.relocate 1524 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_q1 : resolveAt exactSites 1556 = some (AXPair.relocate 1524 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_q2 : resolveAt exactSites 1557 = some (AXPair.relocate 1524 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_q3 : resolveAt exactSites 1558 = some (AXPair.relocate 1524 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_q4 : resolveAt exactSites 1559 = some (AXPair.relocate 1524 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_q5 : resolveAt exactSites 1560 = some (AXPair.relocate 1524 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_q6 : resolveAt exactSites 1561 = some (AXPair.relocate 1524 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_q7 : resolveAt exactSites 1562 = some (AXPair.relocate 1524 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_q8 : resolveAt exactSites 1563 = some (AXPair.relocate 1524 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_q9 : resolveAt exactSites 1564 = some (AXPair.relocate 1524 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1544_q : AXPair.Bound exactSites 1524 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1544_q0
  · exact row1544_q1
  · exact row1544_q2
  · exact row1544_q3
  · exact row1544_q4
  · exact row1544_q5
  · exact row1544_q6
  · exact row1544_q7
  · exact row1544_q8
  · exact row1544_q9
private theorem row1544_m0 : resolveAt exactSites 1565 = some (AXTimes4.expected 1565 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_m1 : resolveAt exactSites 1566 = some (AXTimes4.expected 1565 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_m2 : resolveAt exactSites 1567 = some (AXTimes4.expected 1565 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_m3 : resolveAt exactSites 1568 = some (AXTimes4.expected 1565 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_m4 : resolveAt exactSites 1569 = some (AXTimes4.expected 1565 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1544_m5 : resolveAt exactSites 1570 = some (AXTimes4.expected 1565 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1544_m : AXTimes4.Bound exactSites 1565 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1544_m0
  · exact row1544_m1
  · exact row1544_m2
  · exact row1544_m3
  · exact row1544_m4
  · exact row1544_m5
theorem block1544 : AXMacro.Realizes exactSites .cons 1544 1571 :=
  AXMacro.cons_realizes bound1544_u bound1544_q bound1544_m
private theorem row1571_i0 : resolveAt exactSites 1571 = some (Instruction.inc 1 (some 1572)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block1571 : AXMacro.Realizes exactSites .incT 1571 1572 :=
  AXMacro.inc_realizes row1571_i0
private theorem row1572_i0 : resolveAt exactSites 1572 = some (Instruction.inc 1 (some 1573)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block1572 : AXMacro.Realizes exactSites .incT 1572 1573 :=
  AXMacro.inc_realizes row1572_i0
private theorem row1573_u0 : resolveAt exactSites 1573 = some (UnpairPartial.expected 1573 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_u1 : resolveAt exactSites 1574 = some (UnpairPartial.expected 1573 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_u2 : resolveAt exactSites 1575 = some (UnpairPartial.expected 1573 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_u3 : resolveAt exactSites 1576 = some (UnpairPartial.expected 1573 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_u4 : resolveAt exactSites 1577 = some (UnpairPartial.expected 1573 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_u5 : resolveAt exactSites 1578 = some (UnpairPartial.expected 1573 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_u6 : resolveAt exactSites 1579 = some (UnpairPartial.expected 1573 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_u7 : resolveAt exactSites 1580 = some (UnpairPartial.expected 1573 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_u8 : resolveAt exactSites 1581 = some (UnpairPartial.expected 1573 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_u9 : resolveAt exactSites 1582 = some (UnpairPartial.expected 1573 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_u10 : resolveAt exactSites 1583 = some (UnpairPartial.expected 1573 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1573_u : UnpairPartial.Bound exactSites 1573 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1573_u0
  · exact row1573_u1
  · exact row1573_u2
  · exact row1573_u3
  · exact row1573_u4
  · exact row1573_u5
  · exact row1573_u6
  · exact row1573_u7
  · exact row1573_u8
  · exact row1573_u9
  · exact row1573_u10
private theorem row1573_q0 : resolveAt exactSites 1584 = some (AXPair.relocate 1553 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_q1 : resolveAt exactSites 1585 = some (AXPair.relocate 1553 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_q2 : resolveAt exactSites 1586 = some (AXPair.relocate 1553 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_q3 : resolveAt exactSites 1587 = some (AXPair.relocate 1553 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_q4 : resolveAt exactSites 1588 = some (AXPair.relocate 1553 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_q5 : resolveAt exactSites 1589 = some (AXPair.relocate 1553 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_q6 : resolveAt exactSites 1590 = some (AXPair.relocate 1553 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_q7 : resolveAt exactSites 1591 = some (AXPair.relocate 1553 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_q8 : resolveAt exactSites 1592 = some (AXPair.relocate 1553 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_q9 : resolveAt exactSites 1593 = some (AXPair.relocate 1553 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1573_q : AXPair.Bound exactSites 1553 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1573_q0
  · exact row1573_q1
  · exact row1573_q2
  · exact row1573_q3
  · exact row1573_q4
  · exact row1573_q5
  · exact row1573_q6
  · exact row1573_q7
  · exact row1573_q8
  · exact row1573_q9
private theorem row1573_m0 : resolveAt exactSites 1594 = some (AXTimes4.expected 1594 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_m1 : resolveAt exactSites 1595 = some (AXTimes4.expected 1594 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_m2 : resolveAt exactSites 1596 = some (AXTimes4.expected 1594 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_m3 : resolveAt exactSites 1597 = some (AXTimes4.expected 1594 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_m4 : resolveAt exactSites 1598 = some (AXTimes4.expected 1594 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1573_m5 : resolveAt exactSites 1599 = some (AXTimes4.expected 1594 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1573_m : AXTimes4.Bound exactSites 1594 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1573_m0
  · exact row1573_m1
  · exact row1573_m2
  · exact row1573_m3
  · exact row1573_m4
  · exact row1573_m5
theorem block1573 : AXMacro.Realizes exactSites .cons 1573 1600 :=
  AXMacro.cons_realizes bound1573_u bound1573_q bound1573_m
private theorem row1600_i0 : resolveAt exactSites 1600 = some (Instruction.inc 1 (some 1601)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block1600 : AXMacro.Realizes exactSites .incT 1600 1601 :=
  AXMacro.inc_realizes row1600_i0
private theorem row1601_i0 : resolveAt exactSites 1601 = some (Instruction.inc 1 (some 1602)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block1601 : AXMacro.Realizes exactSites .incT 1601 1602 :=
  AXMacro.inc_realizes row1601_i0
private theorem row1602_p0 : resolveAt exactSites 1602 = some (AXPushParam.relocate 1577 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p1 : resolveAt exactSites 1603 = some (AXPushParam.relocate 1577 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p2 : resolveAt exactSites 1604 = some (AXPushParam.relocate 1577 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p3 : resolveAt exactSites 1605 = some (AXPushParam.relocate 1577 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p4 : resolveAt exactSites 1606 = some (AXPushParam.relocate 1577 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p5 : resolveAt exactSites 1607 = some (AXPushParam.relocate 1577 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p6 : resolveAt exactSites 1608 = some (AXPushParam.relocate 1577 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p7 : resolveAt exactSites 1609 = some (AXPushParam.relocate 1577 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p8 : resolveAt exactSites 1610 = some (AXPushParam.relocate 1577 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p9 : resolveAt exactSites 1611 = some (AXPushParam.relocate 1577 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p10 : resolveAt exactSites 1612 = some (AXPushParam.relocate 1577 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p11 : resolveAt exactSites 1613 = some (AXPushParam.relocate 1577 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p12 : resolveAt exactSites 1614 = some (AXPushParam.relocate 1577 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p13 : resolveAt exactSites 1615 = some (AXPushParam.relocate 1577 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p14 : resolveAt exactSites 1616 = some (AXPushParam.relocate 1577 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p15 : resolveAt exactSites 1617 = some (AXPushParam.relocate 1577 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p16 : resolveAt exactSites 1618 = some (AXPushParam.relocate 1577 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p17 : resolveAt exactSites 1619 = some (AXPushParam.relocate 1577 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1602_p18 : resolveAt exactSites 1620 = some (AXPushParam.relocate 1577 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1602_p : AXPushParam.Bound exactSites 1577 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1602_p0
  · exact row1602_p1
  · exact row1602_p2
  · exact row1602_p3
  · exact row1602_p4
  · exact row1602_p5
  · exact row1602_p6
  · exact row1602_p7
  · exact row1602_p8
  · exact row1602_p9
  · exact row1602_p10
  · exact row1602_p11
  · exact row1602_p12
  · exact row1602_p13
  · exact row1602_p14
  · exact row1602_p15
  · exact row1602_p16
  · exact row1602_p17
  · exact row1602_p18
theorem block1602 : AXMacro.Realizes exactSites .push 1602 1621 :=
  AXMacro.push_realizes bound1602_p
def code009 : List AXMacro.Op := [.copyD,.push,.copyH,.push,.copyA,.cons,.incT,.incT,.cons,.incT,.incT,.push]
theorem plan009 : AXMacro.Plan exactSites 1485 1621 code009 :=
  AXMacro.Plan.cons block1485 ( AXMacro.Plan.cons block1492 ( AXMacro.Plan.cons block1511 ( AXMacro.Plan.cons block1518 ( AXMacro.Plan.cons block1537 ( AXMacro.Plan.cons block1544 ( AXMacro.Plan.cons block1571 ( AXMacro.Plan.cons block1572 ( AXMacro.Plan.cons block1573 ( AXMacro.Plan.cons block1600 ( AXMacro.Plan.cons block1601 ( AXMacro.Plan.cons block1602 ( AXMacro.Plan.nil 1621))))))))))))
#print axioms plan009
end M6.Source.AXAll

