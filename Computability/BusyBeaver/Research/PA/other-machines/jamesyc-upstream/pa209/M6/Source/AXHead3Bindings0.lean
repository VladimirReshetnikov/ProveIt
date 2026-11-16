module
public import M6.Source.AXMacroPlan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXHead3
private theorem row1784_c0 : resolveAt exactSites 1784 = some (CopyToT.expected 4 1784 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1784_c1 : resolveAt exactSites 1785 = some (CopyToT.expected 4 1784 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1784_c2 : resolveAt exactSites 1786 = some (CopyToT.expected 4 1784 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1784_c3 : resolveAt exactSites 1787 = some (CopyToT.expected 4 1784 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1784_c4 : resolveAt exactSites 1788 = some (CopyToT.expected 4 1784 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1784_c5 : resolveAt exactSites 1789 = some (CopyToT.expected 4 1784 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1784_c6 : resolveAt exactSites 1790 = some (CopyToT.expected 4 1784 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1784_c : CopyToT.Bound exactSites 4 1784 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1784_c0
  · exact row1784_c1
  · exact row1784_c2
  · exact row1784_c3
  · exact row1784_c4
  · exact row1784_c5
  · exact row1784_c6
theorem block1784 : AXMacro.Realizes exactSites .copyD 1784 1791 :=
  AXMacro.copyD_realizes bound1784_c
private theorem row1791_p0 : resolveAt exactSites 1791 = some (AXPushParam.relocate 1766 (AXPushParam.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p1 : resolveAt exactSites 1792 = some (AXPushParam.relocate 1766 (AXPushParam.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p2 : resolveAt exactSites 1793 = some (AXPushParam.relocate 1766 (AXPushParam.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p3 : resolveAt exactSites 1794 = some (AXPushParam.relocate 1766 (AXPushParam.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p4 : resolveAt exactSites 1795 = some (AXPushParam.relocate 1766 (AXPushParam.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p5 : resolveAt exactSites 1796 = some (AXPushParam.relocate 1766 (AXPushParam.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p6 : resolveAt exactSites 1797 = some (AXPushParam.relocate 1766 (AXPushParam.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p7 : resolveAt exactSites 1798 = some (AXPushParam.relocate 1766 (AXPushParam.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p8 : resolveAt exactSites 1799 = some (AXPushParam.relocate 1766 (AXPushParam.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p9 : resolveAt exactSites 1800 = some (AXPushParam.relocate 1766 (AXPushParam.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p10 : resolveAt exactSites 1801 = some (AXPushParam.relocate 1766 (AXPushParam.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p11 : resolveAt exactSites 1802 = some (AXPushParam.relocate 1766 (AXPushParam.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p12 : resolveAt exactSites 1803 = some (AXPushParam.relocate 1766 (AXPushParam.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p13 : resolveAt exactSites 1804 = some (AXPushParam.relocate 1766 (AXPushParam.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p14 : resolveAt exactSites 1805 = some (AXPushParam.relocate 1766 (AXPushParam.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p15 : resolveAt exactSites 1806 = some (AXPushParam.relocate 1766 (AXPushParam.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p16 : resolveAt exactSites 1807 = some (AXPushParam.relocate 1766 (AXPushParam.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p17 : resolveAt exactSites 1808 = some (AXPushParam.relocate 1766 (AXPushParam.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1791_p18 : resolveAt exactSites 1809 = some (AXPushParam.relocate 1766 (AXPushParam.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1791_p : AXPushParam.Bound exactSites 1766 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1791_p0
  · exact row1791_p1
  · exact row1791_p2
  · exact row1791_p3
  · exact row1791_p4
  · exact row1791_p5
  · exact row1791_p6
  · exact row1791_p7
  · exact row1791_p8
  · exact row1791_p9
  · exact row1791_p10
  · exact row1791_p11
  · exact row1791_p12
  · exact row1791_p13
  · exact row1791_p14
  · exact row1791_p15
  · exact row1791_p16
  · exact row1791_p17
  · exact row1791_p18
theorem block1791 : AXMacro.Realizes exactSites .push 1791 1810 :=
  AXMacro.push_realizes bound1791_p
private theorem row1810_c0 : resolveAt exactSites 1810 = some (CopyToT.expected 5 1810 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1810_c1 : resolveAt exactSites 1811 = some (CopyToT.expected 5 1810 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1810_c2 : resolveAt exactSites 1812 = some (CopyToT.expected 5 1810 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1810_c3 : resolveAt exactSites 1813 = some (CopyToT.expected 5 1810 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1810_c4 : resolveAt exactSites 1814 = some (CopyToT.expected 5 1810 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1810_c5 : resolveAt exactSites 1815 = some (CopyToT.expected 5 1810 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1810_c6 : resolveAt exactSites 1816 = some (CopyToT.expected 5 1810 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1810_c : CopyToT.Bound exactSites 5 1810 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1810_c0
  · exact row1810_c1
  · exact row1810_c2
  · exact row1810_c3
  · exact row1810_c4
  · exact row1810_c5
  · exact row1810_c6
theorem block1810 : AXMacro.Realizes exactSites .copyH 1810 1817 :=
  AXMacro.copyH_realizes bound1810_c
private theorem row1817_u0 : resolveAt exactSites 1817 = some (UnpairPartial.expected 1817 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_u1 : resolveAt exactSites 1818 = some (UnpairPartial.expected 1817 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_u2 : resolveAt exactSites 1819 = some (UnpairPartial.expected 1817 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_u3 : resolveAt exactSites 1820 = some (UnpairPartial.expected 1817 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_u4 : resolveAt exactSites 1821 = some (UnpairPartial.expected 1817 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_u5 : resolveAt exactSites 1822 = some (UnpairPartial.expected 1817 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_u6 : resolveAt exactSites 1823 = some (UnpairPartial.expected 1817 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_u7 : resolveAt exactSites 1824 = some (UnpairPartial.expected 1817 7) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_u8 : resolveAt exactSites 1825 = some (UnpairPartial.expected 1817 8) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_u9 : resolveAt exactSites 1826 = some (UnpairPartial.expected 1817 9) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_u10 : resolveAt exactSites 1827 = some (UnpairPartial.expected 1817 10) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1817_u : UnpairPartial.Bound exactSites 1817 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1817_u0
  · exact row1817_u1
  · exact row1817_u2
  · exact row1817_u3
  · exact row1817_u4
  · exact row1817_u5
  · exact row1817_u6
  · exact row1817_u7
  · exact row1817_u8
  · exact row1817_u9
  · exact row1817_u10
private theorem row1817_q0 : resolveAt exactSites 1828 = some (AXPair.relocate 1797 (AXPair.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_q1 : resolveAt exactSites 1829 = some (AXPair.relocate 1797 (AXPair.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_q2 : resolveAt exactSites 1830 = some (AXPair.relocate 1797 (AXPair.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_q3 : resolveAt exactSites 1831 = some (AXPair.relocate 1797 (AXPair.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_q4 : resolveAt exactSites 1832 = some (AXPair.relocate 1797 (AXPair.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_q5 : resolveAt exactSites 1833 = some (AXPair.relocate 1797 (AXPair.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_q6 : resolveAt exactSites 1834 = some (AXPair.relocate 1797 (AXPair.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_q7 : resolveAt exactSites 1835 = some (AXPair.relocate 1797 (AXPair.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_q8 : resolveAt exactSites 1836 = some (AXPair.relocate 1797 (AXPair.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_q9 : resolveAt exactSites 1837 = some (AXPair.relocate 1797 (AXPair.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1817_q : AXPair.Bound exactSites 1797 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1817_q0
  · exact row1817_q1
  · exact row1817_q2
  · exact row1817_q3
  · exact row1817_q4
  · exact row1817_q5
  · exact row1817_q6
  · exact row1817_q7
  · exact row1817_q8
  · exact row1817_q9
private theorem row1817_m0 : resolveAt exactSites 1838 = some (AXTimes4.expected 1838 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_m1 : resolveAt exactSites 1839 = some (AXTimes4.expected 1838 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_m2 : resolveAt exactSites 1840 = some (AXTimes4.expected 1838 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_m3 : resolveAt exactSites 1841 = some (AXTimes4.expected 1838 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_m4 : resolveAt exactSites 1842 = some (AXTimes4.expected 1838 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1817_m5 : resolveAt exactSites 1843 = some (AXTimes4.expected 1838 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1817_m : AXTimes4.Bound exactSites 1838 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1817_m0
  · exact row1817_m1
  · exact row1817_m2
  · exact row1817_m3
  · exact row1817_m4
  · exact row1817_m5
theorem block1817 : AXMacro.Realizes exactSites .cons 1817 1844 :=
  AXMacro.cons_realizes bound1817_u bound1817_q bound1817_m
private theorem row1844_i0 : resolveAt exactSites 1844 = some (Instruction.inc 1 (some 1845)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem block1844 : AXMacro.Realizes exactSites .incT 1844 1845 :=
  AXMacro.inc_realizes row1844_i0
private theorem row1845_i0 : resolveAt exactSites 1845 = some (Instruction.inc 1 (some 1846)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem block1845 : AXMacro.Realizes exactSites .incT 1845 1846 :=
  AXMacro.inc_realizes row1845_i0
private theorem row1846_i0 : resolveAt exactSites 1846 = some (Instruction.inc 1 (some 1847)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem block1846 : AXMacro.Realizes exactSites .incT 1846 1847 :=
  AXMacro.inc_realizes row1846_i0
end M6.Source.AXHead3

