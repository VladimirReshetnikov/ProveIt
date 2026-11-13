module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row1765_p0 : resolveAt exactSites 1765 = some (AXPushParam.relocate 1740 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p1 : resolveAt exactSites 1766 = some (AXPushParam.relocate 1740 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p2 : resolveAt exactSites 1767 = some (AXPushParam.relocate 1740 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p3 : resolveAt exactSites 1768 = some (AXPushParam.relocate 1740 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p4 : resolveAt exactSites 1769 = some (AXPushParam.relocate 1740 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p5 : resolveAt exactSites 1770 = some (AXPushParam.relocate 1740 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p6 : resolveAt exactSites 1771 = some (AXPushParam.relocate 1740 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p7 : resolveAt exactSites 1772 = some (AXPushParam.relocate 1740 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p8 : resolveAt exactSites 1773 = some (AXPushParam.relocate 1740 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p9 : resolveAt exactSites 1774 = some (AXPushParam.relocate 1740 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p10 : resolveAt exactSites 1775 = some (AXPushParam.relocate 1740 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p11 : resolveAt exactSites 1776 = some (AXPushParam.relocate 1740 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p12 : resolveAt exactSites 1777 = some (AXPushParam.relocate 1740 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p13 : resolveAt exactSites 1778 = some (AXPushParam.relocate 1740 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p14 : resolveAt exactSites 1779 = some (AXPushParam.relocate 1740 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p15 : resolveAt exactSites 1780 = some (AXPushParam.relocate 1740 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p16 : resolveAt exactSites 1781 = some (AXPushParam.relocate 1740 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p17 : resolveAt exactSites 1782 = some (AXPushParam.relocate 1740 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1765_p18 : resolveAt exactSites 1783 = some (AXPushParam.relocate 1740 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1765_p : AXPushParam.Bound exactSites 1740 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1765_p0
  · exact row1765_p1
  · exact row1765_p2
  · exact row1765_p3
  · exact row1765_p4
  · exact row1765_p5
  · exact row1765_p6
  · exact row1765_p7
  · exact row1765_p8
  · exact row1765_p9
  · exact row1765_p10
  · exact row1765_p11
  · exact row1765_p12
  · exact row1765_p13
  · exact row1765_p14
  · exact row1765_p15
  · exact row1765_p16
  · exact row1765_p17
  · exact row1765_p18
theorem block1765 : AXMacro.Realizes exactSites .push 1765 1784 :=
  AXMacro.push_realizes bound1765_p
theorem block1784 : AXMacro.Realizes exactSites .copyD 1784 1791 := AXHead3.block1784
theorem block1791 : AXMacro.Realizes exactSites .push 1791 1810 := AXHead3.block1791
theorem block1810 : AXMacro.Realizes exactSites .copyH 1810 1817 := AXHead3.block1810
theorem block1817 : AXMacro.Realizes exactSites .cons 1817 1844 := AXHead3.block1817
theorem block1844 : AXMacro.Realizes exactSites .incT 1844 1845 := AXHead3.block1844
theorem block1845 : AXMacro.Realizes exactSites .incT 1845 1846 := AXHead3.block1845
theorem block1846 : AXMacro.Realizes exactSites .incT 1846 1847 := AXHead3.block1846
theorem block1847 : AXMacro.Realizes exactSites .push 1847 1866 := AXHead3.block1847
theorem block1866 : AXMacro.Realizes exactSites .copyA 1866 1873 := AXHead3.block1866
theorem block1873 : AXMacro.Realizes exactSites .push 1873 1892 := AXHead3.block1873
theorem block1892 : AXMacro.Realizes exactSites .copyD 1892 1899 := AXHead3.block1892
def code011 : List AXMacro.Op := [.push,.copyD,.push,.copyH,.cons,.incT,.incT,.incT,.push,.copyA,.push,.copyD]
theorem plan011 : AXMacro.Plan exactSites 1765 1899 code011 :=
  AXMacro.Plan.cons block1765 ( AXMacro.Plan.cons block1784 ( AXMacro.Plan.cons block1791 ( AXMacro.Plan.cons block1810 ( AXMacro.Plan.cons block1817 ( AXMacro.Plan.cons block1844 ( AXMacro.Plan.cons block1845 ( AXMacro.Plan.cons block1846 ( AXMacro.Plan.cons block1847 ( AXMacro.Plan.cons block1866 ( AXMacro.Plan.cons block1873 ( AXMacro.Plan.cons block1892 ( AXMacro.Plan.nil 1899))))))))))))
#print axioms plan011
end M6.Source.AXAll

