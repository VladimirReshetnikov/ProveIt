module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
theorem block1899 : AXMacro.Realizes exactSites .cons 1899 1926 := AXHead3.block1899
theorem block1926 : AXMacro.Realizes exactSites .incT 1926 1927 := AXHead3.block1926
theorem block1927 : AXMacro.Realizes exactSites .push 1927 1946 := AXHead3.block1927
theorem block1946 : AXMacro.Realizes exactSites .copyA 1946 1953 := AXHead3.block1946
theorem block1953 : AXMacro.Realizes exactSites .push 1953 1972 := AXHead3.block1953
theorem block1972 : AXMacro.Realizes exactSites .copyH 1972 1979 := AXHead3.block1972
theorem block1979 : AXMacro.Realizes exactSites .cons 1979 2006 := AXHead3.block1979
theorem block2006 : AXMacro.Realizes exactSites .incT 2006 2007 := AXHead3.block2006
theorem block2007 : AXMacro.Realizes exactSites .cons 2007 2034 := AXHead3.block2007
theorem block2034 : AXMacro.Realizes exactSites .cons 2034 2061 := AXHead3.block2034
private theorem row2061_p0 : resolveAt exactSites 2061 = some (AXPushParam.relocate 2036 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p1 : resolveAt exactSites 2062 = some (AXPushParam.relocate 2036 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p2 : resolveAt exactSites 2063 = some (AXPushParam.relocate 2036 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p3 : resolveAt exactSites 2064 = some (AXPushParam.relocate 2036 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p4 : resolveAt exactSites 2065 = some (AXPushParam.relocate 2036 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p5 : resolveAt exactSites 2066 = some (AXPushParam.relocate 2036 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p6 : resolveAt exactSites 2067 = some (AXPushParam.relocate 2036 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p7 : resolveAt exactSites 2068 = some (AXPushParam.relocate 2036 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p8 : resolveAt exactSites 2069 = some (AXPushParam.relocate 2036 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p9 : resolveAt exactSites 2070 = some (AXPushParam.relocate 2036 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p10 : resolveAt exactSites 2071 = some (AXPushParam.relocate 2036 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p11 : resolveAt exactSites 2072 = some (AXPushParam.relocate 2036 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p12 : resolveAt exactSites 2073 = some (AXPushParam.relocate 2036 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p13 : resolveAt exactSites 2074 = some (AXPushParam.relocate 2036 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p14 : resolveAt exactSites 2075 = some (AXPushParam.relocate 2036 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p15 : resolveAt exactSites 2076 = some (AXPushParam.relocate 2036 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p16 : resolveAt exactSites 2077 = some (AXPushParam.relocate 2036 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p17 : resolveAt exactSites 2078 = some (AXPushParam.relocate 2036 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2061_p18 : resolveAt exactSites 2079 = some (AXPushParam.relocate 2036 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2061_p : AXPushParam.Bound exactSites 2036 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2061_p0
  · exact row2061_p1
  · exact row2061_p2
  · exact row2061_p3
  · exact row2061_p4
  · exact row2061_p5
  · exact row2061_p6
  · exact row2061_p7
  · exact row2061_p8
  · exact row2061_p9
  · exact row2061_p10
  · exact row2061_p11
  · exact row2061_p12
  · exact row2061_p13
  · exact row2061_p14
  · exact row2061_p15
  · exact row2061_p16
  · exact row2061_p17
  · exact row2061_p18
theorem block2061 : AXMacro.Realizes exactSites .push 2061 2080 :=
  AXMacro.push_realizes bound2061_p
private theorem row2080_c0 : resolveAt exactSites 2080 = some (CopyToT.expected 4 2080 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2080_c1 : resolveAt exactSites 2081 = some (CopyToT.expected 4 2080 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2080_c2 : resolveAt exactSites 2082 = some (CopyToT.expected 4 2080 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2080_c3 : resolveAt exactSites 2083 = some (CopyToT.expected 4 2080 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2080_c4 : resolveAt exactSites 2084 = some (CopyToT.expected 4 2080 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2080_c5 : resolveAt exactSites 2085 = some (CopyToT.expected 4 2080 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2080_c6 : resolveAt exactSites 2086 = some (CopyToT.expected 4 2080 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2080_c : CopyToT.Bound exactSites 4 2080 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2080_c0
  · exact row2080_c1
  · exact row2080_c2
  · exact row2080_c3
  · exact row2080_c4
  · exact row2080_c5
  · exact row2080_c6
theorem block2080 : AXMacro.Realizes exactSites .copyD 2080 2087 :=
  AXMacro.copyD_realizes bound2080_c
def code012 : List AXMacro.Op := [.cons,.incT,.push,.copyA,.push,.copyH,.cons,.incT,.cons,.cons,.push,.copyD]
theorem plan012 : AXMacro.Plan exactSites 1899 2087 code012 :=
  AXMacro.Plan.cons block1899 ( AXMacro.Plan.cons block1926 ( AXMacro.Plan.cons block1927 ( AXMacro.Plan.cons block1946 ( AXMacro.Plan.cons block1953 ( AXMacro.Plan.cons block1972 ( AXMacro.Plan.cons block1979 ( AXMacro.Plan.cons block2006 ( AXMacro.Plan.cons block2007 ( AXMacro.Plan.cons block2034 ( AXMacro.Plan.cons block2061 ( AXMacro.Plan.cons block2080 ( AXMacro.Plan.nil 2087))))))))))))
#print axioms plan012
end M6.Source.AXAll

