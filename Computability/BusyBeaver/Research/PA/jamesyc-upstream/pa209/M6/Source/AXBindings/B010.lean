module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row1621_c0 : resolveAt exactSites 1621 = some (CopyToT.expected 5 1621 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1621_c1 : resolveAt exactSites 1622 = some (CopyToT.expected 5 1621 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1621_c2 : resolveAt exactSites 1623 = some (CopyToT.expected 5 1621 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1621_c3 : resolveAt exactSites 1624 = some (CopyToT.expected 5 1621 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1621_c4 : resolveAt exactSites 1625 = some (CopyToT.expected 5 1621 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1621_c5 : resolveAt exactSites 1626 = some (CopyToT.expected 5 1621 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1621_c6 : resolveAt exactSites 1627 = some (CopyToT.expected 5 1621 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1621_c : CopyToT.Bound exactSites 5 1621 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1621_c0
  · exact row1621_c1
  · exact row1621_c2
  · exact row1621_c3
  · exact row1621_c4
  · exact row1621_c5
  · exact row1621_c6
theorem block1621 : AXMacro.Realizes exactSites .copyH 1621 1628 :=
  AXMacro.copyH_realizes bound1621_c
private theorem row1628_p0 : resolveAt exactSites 1628 = some (AXPushParam.relocate 1603 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p1 : resolveAt exactSites 1629 = some (AXPushParam.relocate 1603 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p2 : resolveAt exactSites 1630 = some (AXPushParam.relocate 1603 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p3 : resolveAt exactSites 1631 = some (AXPushParam.relocate 1603 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p4 : resolveAt exactSites 1632 = some (AXPushParam.relocate 1603 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p5 : resolveAt exactSites 1633 = some (AXPushParam.relocate 1603 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p6 : resolveAt exactSites 1634 = some (AXPushParam.relocate 1603 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p7 : resolveAt exactSites 1635 = some (AXPushParam.relocate 1603 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p8 : resolveAt exactSites 1636 = some (AXPushParam.relocate 1603 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p9 : resolveAt exactSites 1637 = some (AXPushParam.relocate 1603 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p10 : resolveAt exactSites 1638 = some (AXPushParam.relocate 1603 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p11 : resolveAt exactSites 1639 = some (AXPushParam.relocate 1603 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p12 : resolveAt exactSites 1640 = some (AXPushParam.relocate 1603 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p13 : resolveAt exactSites 1641 = some (AXPushParam.relocate 1603 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p14 : resolveAt exactSites 1642 = some (AXPushParam.relocate 1603 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p15 : resolveAt exactSites 1643 = some (AXPushParam.relocate 1603 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p16 : resolveAt exactSites 1644 = some (AXPushParam.relocate 1603 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p17 : resolveAt exactSites 1645 = some (AXPushParam.relocate 1603 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1628_p18 : resolveAt exactSites 1646 = some (AXPushParam.relocate 1603 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1628_p : AXPushParam.Bound exactSites 1603 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1628_p0
  · exact row1628_p1
  · exact row1628_p2
  · exact row1628_p3
  · exact row1628_p4
  · exact row1628_p5
  · exact row1628_p6
  · exact row1628_p7
  · exact row1628_p8
  · exact row1628_p9
  · exact row1628_p10
  · exact row1628_p11
  · exact row1628_p12
  · exact row1628_p13
  · exact row1628_p14
  · exact row1628_p15
  · exact row1628_p16
  · exact row1628_p17
  · exact row1628_p18
theorem block1628 : AXMacro.Realizes exactSites .push 1628 1647 :=
  AXMacro.push_realizes bound1628_p
private theorem row1647_c0 : resolveAt exactSites 1647 = some (CopyToT.expected 4 1647 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1647_c1 : resolveAt exactSites 1648 = some (CopyToT.expected 4 1647 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1647_c2 : resolveAt exactSites 1649 = some (CopyToT.expected 4 1647 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1647_c3 : resolveAt exactSites 1650 = some (CopyToT.expected 4 1647 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1647_c4 : resolveAt exactSites 1651 = some (CopyToT.expected 4 1647 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1647_c5 : resolveAt exactSites 1652 = some (CopyToT.expected 4 1647 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1647_c6 : resolveAt exactSites 1653 = some (CopyToT.expected 4 1647 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1647_c : CopyToT.Bound exactSites 4 1647 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1647_c0
  · exact row1647_c1
  · exact row1647_c2
  · exact row1647_c3
  · exact row1647_c4
  · exact row1647_c5
  · exact row1647_c6
theorem block1647 : AXMacro.Realizes exactSites .copyD 1647 1654 :=
  AXMacro.copyD_realizes bound1647_c
private theorem row1654_p0 : resolveAt exactSites 1654 = some (AXPushParam.relocate 1629 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p1 : resolveAt exactSites 1655 = some (AXPushParam.relocate 1629 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p2 : resolveAt exactSites 1656 = some (AXPushParam.relocate 1629 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p3 : resolveAt exactSites 1657 = some (AXPushParam.relocate 1629 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p4 : resolveAt exactSites 1658 = some (AXPushParam.relocate 1629 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p5 : resolveAt exactSites 1659 = some (AXPushParam.relocate 1629 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p6 : resolveAt exactSites 1660 = some (AXPushParam.relocate 1629 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p7 : resolveAt exactSites 1661 = some (AXPushParam.relocate 1629 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p8 : resolveAt exactSites 1662 = some (AXPushParam.relocate 1629 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p9 : resolveAt exactSites 1663 = some (AXPushParam.relocate 1629 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p10 : resolveAt exactSites 1664 = some (AXPushParam.relocate 1629 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p11 : resolveAt exactSites 1665 = some (AXPushParam.relocate 1629 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p12 : resolveAt exactSites 1666 = some (AXPushParam.relocate 1629 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p13 : resolveAt exactSites 1667 = some (AXPushParam.relocate 1629 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p14 : resolveAt exactSites 1668 = some (AXPushParam.relocate 1629 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p15 : resolveAt exactSites 1669 = some (AXPushParam.relocate 1629 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p16 : resolveAt exactSites 1670 = some (AXPushParam.relocate 1629 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p17 : resolveAt exactSites 1671 = some (AXPushParam.relocate 1629 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1654_p18 : resolveAt exactSites 1672 = some (AXPushParam.relocate 1629 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1654_p : AXPushParam.Bound exactSites 1629 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1654_p0
  · exact row1654_p1
  · exact row1654_p2
  · exact row1654_p3
  · exact row1654_p4
  · exact row1654_p5
  · exact row1654_p6
  · exact row1654_p7
  · exact row1654_p8
  · exact row1654_p9
  · exact row1654_p10
  · exact row1654_p11
  · exact row1654_p12
  · exact row1654_p13
  · exact row1654_p14
  · exact row1654_p15
  · exact row1654_p16
  · exact row1654_p17
  · exact row1654_p18
theorem block1654 : AXMacro.Realizes exactSites .push 1654 1673 :=
  AXMacro.push_realizes bound1654_p
private theorem row1673_c0 : resolveAt exactSites 1673 = some (CopyToT.expected 3 1673 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1673_c1 : resolveAt exactSites 1674 = some (CopyToT.expected 3 1673 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1673_c2 : resolveAt exactSites 1675 = some (CopyToT.expected 3 1673 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1673_c3 : resolveAt exactSites 1676 = some (CopyToT.expected 3 1673 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1673_c4 : resolveAt exactSites 1677 = some (CopyToT.expected 3 1673 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1673_c5 : resolveAt exactSites 1678 = some (CopyToT.expected 3 1673 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1673_c6 : resolveAt exactSites 1679 = some (CopyToT.expected 3 1673 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1673_c : CopyToT.Bound exactSites 3 1673 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1673_c0
  · exact row1673_c1
  · exact row1673_c2
  · exact row1673_c3
  · exact row1673_c4
  · exact row1673_c5
  · exact row1673_c6
theorem block1673 : AXMacro.Realizes exactSites .copyA 1673 1680 :=
  AXMacro.copyA_realizes bound1673_c
private theorem row1680_u0 : resolveAt exactSites 1680 = some (UnpairPartial.expected 1680 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_u1 : resolveAt exactSites 1681 = some (UnpairPartial.expected 1680 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_u2 : resolveAt exactSites 1682 = some (UnpairPartial.expected 1680 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_u3 : resolveAt exactSites 1683 = some (UnpairPartial.expected 1680 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_u4 : resolveAt exactSites 1684 = some (UnpairPartial.expected 1680 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_u5 : resolveAt exactSites 1685 = some (UnpairPartial.expected 1680 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_u6 : resolveAt exactSites 1686 = some (UnpairPartial.expected 1680 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_u7 : resolveAt exactSites 1687 = some (UnpairPartial.expected 1680 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_u8 : resolveAt exactSites 1688 = some (UnpairPartial.expected 1680 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_u9 : resolveAt exactSites 1689 = some (UnpairPartial.expected 1680 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_u10 : resolveAt exactSites 1690 = some (UnpairPartial.expected 1680 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1680_u : UnpairPartial.Bound exactSites 1680 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1680_u0
  · exact row1680_u1
  · exact row1680_u2
  · exact row1680_u3
  · exact row1680_u4
  · exact row1680_u5
  · exact row1680_u6
  · exact row1680_u7
  · exact row1680_u8
  · exact row1680_u9
  · exact row1680_u10
private theorem row1680_q0 : resolveAt exactSites 1691 = some (AXPair.relocate 1660 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_q1 : resolveAt exactSites 1692 = some (AXPair.relocate 1660 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_q2 : resolveAt exactSites 1693 = some (AXPair.relocate 1660 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_q3 : resolveAt exactSites 1694 = some (AXPair.relocate 1660 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_q4 : resolveAt exactSites 1695 = some (AXPair.relocate 1660 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_q5 : resolveAt exactSites 1696 = some (AXPair.relocate 1660 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_q6 : resolveAt exactSites 1697 = some (AXPair.relocate 1660 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_q7 : resolveAt exactSites 1698 = some (AXPair.relocate 1660 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_q8 : resolveAt exactSites 1699 = some (AXPair.relocate 1660 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_q9 : resolveAt exactSites 1700 = some (AXPair.relocate 1660 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1680_q : AXPair.Bound exactSites 1660 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1680_q0
  · exact row1680_q1
  · exact row1680_q2
  · exact row1680_q3
  · exact row1680_q4
  · exact row1680_q5
  · exact row1680_q6
  · exact row1680_q7
  · exact row1680_q8
  · exact row1680_q9
private theorem row1680_m0 : resolveAt exactSites 1701 = some (AXTimes4.expected 1701 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_m1 : resolveAt exactSites 1702 = some (AXTimes4.expected 1701 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_m2 : resolveAt exactSites 1703 = some (AXTimes4.expected 1701 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_m3 : resolveAt exactSites 1704 = some (AXTimes4.expected 1701 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_m4 : resolveAt exactSites 1705 = some (AXTimes4.expected 1701 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1680_m5 : resolveAt exactSites 1706 = some (AXTimes4.expected 1701 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1680_m : AXTimes4.Bound exactSites 1701 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1680_m0
  · exact row1680_m1
  · exact row1680_m2
  · exact row1680_m3
  · exact row1680_m4
  · exact row1680_m5
theorem block1680 : AXMacro.Realizes exactSites .cons 1680 1707 :=
  AXMacro.cons_realizes bound1680_u bound1680_q bound1680_m
private theorem row1707_i0 : resolveAt exactSites 1707 = some (Instruction.inc 1 (some 1708)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block1707 : AXMacro.Realizes exactSites .incT 1707 1708 :=
  AXMacro.inc_realizes row1707_i0
private theorem row1708_i0 : resolveAt exactSites 1708 = some (Instruction.inc 1 (some 1709)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block1708 : AXMacro.Realizes exactSites .incT 1708 1709 :=
  AXMacro.inc_realizes row1708_i0
private theorem row1709_u0 : resolveAt exactSites 1709 = some (UnpairPartial.expected 1709 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_u1 : resolveAt exactSites 1710 = some (UnpairPartial.expected 1709 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_u2 : resolveAt exactSites 1711 = some (UnpairPartial.expected 1709 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_u3 : resolveAt exactSites 1712 = some (UnpairPartial.expected 1709 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_u4 : resolveAt exactSites 1713 = some (UnpairPartial.expected 1709 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_u5 : resolveAt exactSites 1714 = some (UnpairPartial.expected 1709 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_u6 : resolveAt exactSites 1715 = some (UnpairPartial.expected 1709 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_u7 : resolveAt exactSites 1716 = some (UnpairPartial.expected 1709 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_u8 : resolveAt exactSites 1717 = some (UnpairPartial.expected 1709 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_u9 : resolveAt exactSites 1718 = some (UnpairPartial.expected 1709 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_u10 : resolveAt exactSites 1719 = some (UnpairPartial.expected 1709 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1709_u : UnpairPartial.Bound exactSites 1709 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1709_u0
  · exact row1709_u1
  · exact row1709_u2
  · exact row1709_u3
  · exact row1709_u4
  · exact row1709_u5
  · exact row1709_u6
  · exact row1709_u7
  · exact row1709_u8
  · exact row1709_u9
  · exact row1709_u10
private theorem row1709_q0 : resolveAt exactSites 1720 = some (AXPair.relocate 1689 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_q1 : resolveAt exactSites 1721 = some (AXPair.relocate 1689 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_q2 : resolveAt exactSites 1722 = some (AXPair.relocate 1689 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_q3 : resolveAt exactSites 1723 = some (AXPair.relocate 1689 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_q4 : resolveAt exactSites 1724 = some (AXPair.relocate 1689 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_q5 : resolveAt exactSites 1725 = some (AXPair.relocate 1689 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_q6 : resolveAt exactSites 1726 = some (AXPair.relocate 1689 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_q7 : resolveAt exactSites 1727 = some (AXPair.relocate 1689 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_q8 : resolveAt exactSites 1728 = some (AXPair.relocate 1689 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_q9 : resolveAt exactSites 1729 = some (AXPair.relocate 1689 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1709_q : AXPair.Bound exactSites 1689 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1709_q0
  · exact row1709_q1
  · exact row1709_q2
  · exact row1709_q3
  · exact row1709_q4
  · exact row1709_q5
  · exact row1709_q6
  · exact row1709_q7
  · exact row1709_q8
  · exact row1709_q9
private theorem row1709_m0 : resolveAt exactSites 1730 = some (AXTimes4.expected 1730 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_m1 : resolveAt exactSites 1731 = some (AXTimes4.expected 1730 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_m2 : resolveAt exactSites 1732 = some (AXTimes4.expected 1730 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_m3 : resolveAt exactSites 1733 = some (AXTimes4.expected 1730 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_m4 : resolveAt exactSites 1734 = some (AXTimes4.expected 1730 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1709_m5 : resolveAt exactSites 1735 = some (AXTimes4.expected 1730 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1709_m : AXTimes4.Bound exactSites 1730 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1709_m0
  · exact row1709_m1
  · exact row1709_m2
  · exact row1709_m3
  · exact row1709_m4
  · exact row1709_m5
theorem block1709 : AXMacro.Realizes exactSites .cons 1709 1736 :=
  AXMacro.cons_realizes bound1709_u bound1709_q bound1709_m
private theorem row1736_i0 : resolveAt exactSites 1736 = some (Instruction.inc 1 (some 1737)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block1736 : AXMacro.Realizes exactSites .incT 1736 1737 :=
  AXMacro.inc_realizes row1736_i0
private theorem row1737_i0 : resolveAt exactSites 1737 = some (Instruction.inc 1 (some 1738)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block1737 : AXMacro.Realizes exactSites .incT 1737 1738 :=
  AXMacro.inc_realizes row1737_i0
private theorem row1738_u0 : resolveAt exactSites 1738 = some (UnpairPartial.expected 1738 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_u1 : resolveAt exactSites 1739 = some (UnpairPartial.expected 1738 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_u2 : resolveAt exactSites 1740 = some (UnpairPartial.expected 1738 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_u3 : resolveAt exactSites 1741 = some (UnpairPartial.expected 1738 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_u4 : resolveAt exactSites 1742 = some (UnpairPartial.expected 1738 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_u5 : resolveAt exactSites 1743 = some (UnpairPartial.expected 1738 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_u6 : resolveAt exactSites 1744 = some (UnpairPartial.expected 1738 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_u7 : resolveAt exactSites 1745 = some (UnpairPartial.expected 1738 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_u8 : resolveAt exactSites 1746 = some (UnpairPartial.expected 1738 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_u9 : resolveAt exactSites 1747 = some (UnpairPartial.expected 1738 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_u10 : resolveAt exactSites 1748 = some (UnpairPartial.expected 1738 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1738_u : UnpairPartial.Bound exactSites 1738 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1738_u0
  · exact row1738_u1
  · exact row1738_u2
  · exact row1738_u3
  · exact row1738_u4
  · exact row1738_u5
  · exact row1738_u6
  · exact row1738_u7
  · exact row1738_u8
  · exact row1738_u9
  · exact row1738_u10
private theorem row1738_q0 : resolveAt exactSites 1749 = some (AXPair.relocate 1718 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_q1 : resolveAt exactSites 1750 = some (AXPair.relocate 1718 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_q2 : resolveAt exactSites 1751 = some (AXPair.relocate 1718 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_q3 : resolveAt exactSites 1752 = some (AXPair.relocate 1718 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_q4 : resolveAt exactSites 1753 = some (AXPair.relocate 1718 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_q5 : resolveAt exactSites 1754 = some (AXPair.relocate 1718 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_q6 : resolveAt exactSites 1755 = some (AXPair.relocate 1718 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_q7 : resolveAt exactSites 1756 = some (AXPair.relocate 1718 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_q8 : resolveAt exactSites 1757 = some (AXPair.relocate 1718 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_q9 : resolveAt exactSites 1758 = some (AXPair.relocate 1718 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1738_q : AXPair.Bound exactSites 1718 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1738_q0
  · exact row1738_q1
  · exact row1738_q2
  · exact row1738_q3
  · exact row1738_q4
  · exact row1738_q5
  · exact row1738_q6
  · exact row1738_q7
  · exact row1738_q8
  · exact row1738_q9
private theorem row1738_m0 : resolveAt exactSites 1759 = some (AXTimes4.expected 1759 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_m1 : resolveAt exactSites 1760 = some (AXTimes4.expected 1759 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_m2 : resolveAt exactSites 1761 = some (AXTimes4.expected 1759 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_m3 : resolveAt exactSites 1762 = some (AXTimes4.expected 1759 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_m4 : resolveAt exactSites 1763 = some (AXTimes4.expected 1759 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1738_m5 : resolveAt exactSites 1764 = some (AXTimes4.expected 1759 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1738_m : AXTimes4.Bound exactSites 1759 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1738_m0
  · exact row1738_m1
  · exact row1738_m2
  · exact row1738_m3
  · exact row1738_m4
  · exact row1738_m5
theorem block1738 : AXMacro.Realizes exactSites .cons 1738 1765 :=
  AXMacro.cons_realizes bound1738_u bound1738_q bound1738_m
def code010 : List AXMacro.Op := [.copyH,.push,.copyD,.push,.copyA,.cons,.incT,.incT,.cons,.incT,.incT,.cons]
theorem plan010 : AXMacro.Plan exactSites 1621 1765 code010 :=
  AXMacro.Plan.cons block1621 ( AXMacro.Plan.cons block1628 ( AXMacro.Plan.cons block1647 ( AXMacro.Plan.cons block1654 ( AXMacro.Plan.cons block1673 ( AXMacro.Plan.cons block1680 ( AXMacro.Plan.cons block1707 ( AXMacro.Plan.cons block1708 ( AXMacro.Plan.cons block1709 ( AXMacro.Plan.cons block1736 ( AXMacro.Plan.cons block1737 ( AXMacro.Plan.cons block1738 ( AXMacro.Plan.nil 1765))))))))))))
#print axioms plan010
end M6.Source.AXAll

