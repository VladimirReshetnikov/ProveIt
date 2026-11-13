module
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row25_p0 : resolveAt exactSites 25 = some (AXPushParam.relocate 0 (AXPushParam.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p1 : resolveAt exactSites 26 = some (AXPushParam.relocate 0 (AXPushParam.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p2 : resolveAt exactSites 27 = some (AXPushParam.relocate 0 (AXPushParam.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p3 : resolveAt exactSites 28 = some (AXPushParam.relocate 0 (AXPushParam.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p4 : resolveAt exactSites 29 = some (AXPushParam.relocate 0 (AXPushParam.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p5 : resolveAt exactSites 30 = some (AXPushParam.relocate 0 (AXPushParam.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p6 : resolveAt exactSites 31 = some (AXPushParam.relocate 0 (AXPushParam.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p7 : resolveAt exactSites 32 = some (AXPushParam.relocate 0 (AXPushParam.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p8 : resolveAt exactSites 33 = some (AXPushParam.relocate 0 (AXPushParam.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p9 : resolveAt exactSites 34 = some (AXPushParam.relocate 0 (AXPushParam.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p10 : resolveAt exactSites 35 = some (AXPushParam.relocate 0 (AXPushParam.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p11 : resolveAt exactSites 36 = some (AXPushParam.relocate 0 (AXPushParam.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p12 : resolveAt exactSites 37 = some (AXPushParam.relocate 0 (AXPushParam.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p13 : resolveAt exactSites 38 = some (AXPushParam.relocate 0 (AXPushParam.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p14 : resolveAt exactSites 39 = some (AXPushParam.relocate 0 (AXPushParam.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p15 : resolveAt exactSites 40 = some (AXPushParam.relocate 0 (AXPushParam.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p16 : resolveAt exactSites 41 = some (AXPushParam.relocate 0 (AXPushParam.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p17 : resolveAt exactSites 42 = some (AXPushParam.relocate 0 (AXPushParam.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row25_p18 : resolveAt exactSites 43 = some (AXPushParam.relocate 0 (AXPushParam.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound25_p : AXPushParam.Bound exactSites 0 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row25_p0
  · exact row25_p1
  · exact row25_p2
  · exact row25_p3
  · exact row25_p4
  · exact row25_p5
  · exact row25_p6
  · exact row25_p7
  · exact row25_p8
  · exact row25_p9
  · exact row25_p10
  · exact row25_p11
  · exact row25_p12
  · exact row25_p13
  · exact row25_p14
  · exact row25_p15
  · exact row25_p16
  · exact row25_p17
  · exact row25_p18
theorem block25 : AXMacro.Realizes exactSites .push 25 44 :=
  AXMacro.push_realizes bound25_p
private theorem row44_c0 : resolveAt exactSites 44 = some (CopyToT.expected 4 44 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row44_c1 : resolveAt exactSites 45 = some (CopyToT.expected 4 44 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row44_c2 : resolveAt exactSites 46 = some (CopyToT.expected 4 44 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row44_c3 : resolveAt exactSites 47 = some (CopyToT.expected 4 44 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row44_c4 : resolveAt exactSites 48 = some (CopyToT.expected 4 44 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row44_c5 : resolveAt exactSites 49 = some (CopyToT.expected 4 44 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row44_c6 : resolveAt exactSites 50 = some (CopyToT.expected 4 44 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound44_c : CopyToT.Bound exactSites 4 44 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row44_c0
  · exact row44_c1
  · exact row44_c2
  · exact row44_c3
  · exact row44_c4
  · exact row44_c5
  · exact row44_c6
theorem block44 : AXMacro.Realizes exactSites .copyD 44 51 :=
  AXMacro.copyD_realizes bound44_c
private theorem row51_p0 : resolveAt exactSites 51 = some (AXPushParam.relocate 26 (AXPushParam.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p1 : resolveAt exactSites 52 = some (AXPushParam.relocate 26 (AXPushParam.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p2 : resolveAt exactSites 53 = some (AXPushParam.relocate 26 (AXPushParam.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p3 : resolveAt exactSites 54 = some (AXPushParam.relocate 26 (AXPushParam.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p4 : resolveAt exactSites 55 = some (AXPushParam.relocate 26 (AXPushParam.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p5 : resolveAt exactSites 56 = some (AXPushParam.relocate 26 (AXPushParam.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p6 : resolveAt exactSites 57 = some (AXPushParam.relocate 26 (AXPushParam.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p7 : resolveAt exactSites 58 = some (AXPushParam.relocate 26 (AXPushParam.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p8 : resolveAt exactSites 59 = some (AXPushParam.relocate 26 (AXPushParam.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p9 : resolveAt exactSites 60 = some (AXPushParam.relocate 26 (AXPushParam.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p10 : resolveAt exactSites 61 = some (AXPushParam.relocate 26 (AXPushParam.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p11 : resolveAt exactSites 62 = some (AXPushParam.relocate 26 (AXPushParam.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p12 : resolveAt exactSites 63 = some (AXPushParam.relocate 26 (AXPushParam.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p13 : resolveAt exactSites 64 = some (AXPushParam.relocate 26 (AXPushParam.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p14 : resolveAt exactSites 65 = some (AXPushParam.relocate 26 (AXPushParam.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p15 : resolveAt exactSites 66 = some (AXPushParam.relocate 26 (AXPushParam.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p16 : resolveAt exactSites 67 = some (AXPushParam.relocate 26 (AXPushParam.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p17 : resolveAt exactSites 68 = some (AXPushParam.relocate 26 (AXPushParam.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row51_p18 : resolveAt exactSites 69 = some (AXPushParam.relocate 26 (AXPushParam.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound51_p : AXPushParam.Bound exactSites 26 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row51_p0
  · exact row51_p1
  · exact row51_p2
  · exact row51_p3
  · exact row51_p4
  · exact row51_p5
  · exact row51_p6
  · exact row51_p7
  · exact row51_p8
  · exact row51_p9
  · exact row51_p10
  · exact row51_p11
  · exact row51_p12
  · exact row51_p13
  · exact row51_p14
  · exact row51_p15
  · exact row51_p16
  · exact row51_p17
  · exact row51_p18
theorem block51 : AXMacro.Realizes exactSites .push 51 70 :=
  AXMacro.push_realizes bound51_p
private theorem row70_c0 : resolveAt exactSites 70 = some (CopyToT.expected 5 70 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row70_c1 : resolveAt exactSites 71 = some (CopyToT.expected 5 70 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row70_c2 : resolveAt exactSites 72 = some (CopyToT.expected 5 70 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row70_c3 : resolveAt exactSites 73 = some (CopyToT.expected 5 70 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row70_c4 : resolveAt exactSites 74 = some (CopyToT.expected 5 70 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row70_c5 : resolveAt exactSites 75 = some (CopyToT.expected 5 70 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row70_c6 : resolveAt exactSites 76 = some (CopyToT.expected 5 70 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound70_c : CopyToT.Bound exactSites 5 70 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row70_c0
  · exact row70_c1
  · exact row70_c2
  · exact row70_c3
  · exact row70_c4
  · exact row70_c5
  · exact row70_c6
theorem block70 : AXMacro.Realizes exactSites .copyH 70 77 :=
  AXMacro.copyH_realizes bound70_c
private theorem row77_u0 : resolveAt exactSites 77 = some (UnpairPartial.expected 77 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_u1 : resolveAt exactSites 78 = some (UnpairPartial.expected 77 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_u2 : resolveAt exactSites 79 = some (UnpairPartial.expected 77 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_u3 : resolveAt exactSites 80 = some (UnpairPartial.expected 77 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_u4 : resolveAt exactSites 81 = some (UnpairPartial.expected 77 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_u5 : resolveAt exactSites 82 = some (UnpairPartial.expected 77 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_u6 : resolveAt exactSites 83 = some (UnpairPartial.expected 77 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_u7 : resolveAt exactSites 84 = some (UnpairPartial.expected 77 7) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_u8 : resolveAt exactSites 85 = some (UnpairPartial.expected 77 8) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_u9 : resolveAt exactSites 86 = some (UnpairPartial.expected 77 9) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_u10 : resolveAt exactSites 87 = some (UnpairPartial.expected 77 10) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound77_u : UnpairPartial.Bound exactSites 77 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row77_u0
  · exact row77_u1
  · exact row77_u2
  · exact row77_u3
  · exact row77_u4
  · exact row77_u5
  · exact row77_u6
  · exact row77_u7
  · exact row77_u8
  · exact row77_u9
  · exact row77_u10
private theorem row77_q0 : resolveAt exactSites 88 = some (AXPair.relocate 57 (AXPair.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_q1 : resolveAt exactSites 89 = some (AXPair.relocate 57 (AXPair.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_q2 : resolveAt exactSites 90 = some (AXPair.relocate 57 (AXPair.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_q3 : resolveAt exactSites 91 = some (AXPair.relocate 57 (AXPair.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_q4 : resolveAt exactSites 92 = some (AXPair.relocate 57 (AXPair.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_q5 : resolveAt exactSites 93 = some (AXPair.relocate 57 (AXPair.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_q6 : resolveAt exactSites 94 = some (AXPair.relocate 57 (AXPair.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_q7 : resolveAt exactSites 95 = some (AXPair.relocate 57 (AXPair.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_q8 : resolveAt exactSites 96 = some (AXPair.relocate 57 (AXPair.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_q9 : resolveAt exactSites 97 = some (AXPair.relocate 57 (AXPair.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound77_q : AXPair.Bound exactSites 57 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row77_q0
  · exact row77_q1
  · exact row77_q2
  · exact row77_q3
  · exact row77_q4
  · exact row77_q5
  · exact row77_q6
  · exact row77_q7
  · exact row77_q8
  · exact row77_q9
private theorem row77_m0 : resolveAt exactSites 98 = some (AXTimes4.expected 98 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_m1 : resolveAt exactSites 99 = some (AXTimes4.expected 98 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_m2 : resolveAt exactSites 100 = some (AXTimes4.expected 98 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_m3 : resolveAt exactSites 101 = some (AXTimes4.expected 98 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_m4 : resolveAt exactSites 102 = some (AXTimes4.expected 98 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row77_m5 : resolveAt exactSites 103 = some (AXTimes4.expected 98 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound77_m : AXTimes4.Bound exactSites 98 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row77_m0
  · exact row77_m1
  · exact row77_m2
  · exact row77_m3
  · exact row77_m4
  · exact row77_m5
theorem block77 : AXMacro.Realizes exactSites .cons 77 104 :=
  AXMacro.cons_realizes bound77_u bound77_q bound77_m
private theorem row104_i0 : resolveAt exactSites 104 = some (Instruction.inc 1 (some 105)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem block104 : AXMacro.Realizes exactSites .incT 104 105 :=
  AXMacro.inc_realizes row104_i0
private theorem row105_i0 : resolveAt exactSites 105 = some (Instruction.inc 1 (some 106)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem block105 : AXMacro.Realizes exactSites .incT 105 106 :=
  AXMacro.inc_realizes row105_i0
private theorem row106_p0 : resolveAt exactSites 106 = some (AXPushParam.relocate 81 (AXPushParam.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p1 : resolveAt exactSites 107 = some (AXPushParam.relocate 81 (AXPushParam.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p2 : resolveAt exactSites 108 = some (AXPushParam.relocate 81 (AXPushParam.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p3 : resolveAt exactSites 109 = some (AXPushParam.relocate 81 (AXPushParam.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p4 : resolveAt exactSites 110 = some (AXPushParam.relocate 81 (AXPushParam.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p5 : resolveAt exactSites 111 = some (AXPushParam.relocate 81 (AXPushParam.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p6 : resolveAt exactSites 112 = some (AXPushParam.relocate 81 (AXPushParam.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p7 : resolveAt exactSites 113 = some (AXPushParam.relocate 81 (AXPushParam.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p8 : resolveAt exactSites 114 = some (AXPushParam.relocate 81 (AXPushParam.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p9 : resolveAt exactSites 115 = some (AXPushParam.relocate 81 (AXPushParam.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p10 : resolveAt exactSites 116 = some (AXPushParam.relocate 81 (AXPushParam.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p11 : resolveAt exactSites 117 = some (AXPushParam.relocate 81 (AXPushParam.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p12 : resolveAt exactSites 118 = some (AXPushParam.relocate 81 (AXPushParam.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p13 : resolveAt exactSites 119 = some (AXPushParam.relocate 81 (AXPushParam.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p14 : resolveAt exactSites 120 = some (AXPushParam.relocate 81 (AXPushParam.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p15 : resolveAt exactSites 121 = some (AXPushParam.relocate 81 (AXPushParam.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p16 : resolveAt exactSites 122 = some (AXPushParam.relocate 81 (AXPushParam.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p17 : resolveAt exactSites 123 = some (AXPushParam.relocate 81 (AXPushParam.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row106_p18 : resolveAt exactSites 124 = some (AXPushParam.relocate 81 (AXPushParam.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound106_p : AXPushParam.Bound exactSites 81 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row106_p0
  · exact row106_p1
  · exact row106_p2
  · exact row106_p3
  · exact row106_p4
  · exact row106_p5
  · exact row106_p6
  · exact row106_p7
  · exact row106_p8
  · exact row106_p9
  · exact row106_p10
  · exact row106_p11
  · exact row106_p12
  · exact row106_p13
  · exact row106_p14
  · exact row106_p15
  · exact row106_p16
  · exact row106_p17
  · exact row106_p18
theorem block106 : AXMacro.Realizes exactSites .push 106 125 :=
  AXMacro.push_realizes bound106_p
private theorem row125_c0 : resolveAt exactSites 125 = some (CopyToT.expected 3 125 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row125_c1 : resolveAt exactSites 126 = some (CopyToT.expected 3 125 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row125_c2 : resolveAt exactSites 127 = some (CopyToT.expected 3 125 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row125_c3 : resolveAt exactSites 128 = some (CopyToT.expected 3 125 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row125_c4 : resolveAt exactSites 129 = some (CopyToT.expected 3 125 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row125_c5 : resolveAt exactSites 130 = some (CopyToT.expected 3 125 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row125_c6 : resolveAt exactSites 131 = some (CopyToT.expected 3 125 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound125_c : CopyToT.Bound exactSites 3 125 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row125_c0
  · exact row125_c1
  · exact row125_c2
  · exact row125_c3
  · exact row125_c4
  · exact row125_c5
  · exact row125_c6
theorem block125 : AXMacro.Realizes exactSites .copyA 125 132 :=
  AXMacro.copyA_realizes bound125_c
private theorem row132_p0 : resolveAt exactSites 132 = some (AXPushParam.relocate 107 (AXPushParam.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p1 : resolveAt exactSites 133 = some (AXPushParam.relocate 107 (AXPushParam.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p2 : resolveAt exactSites 134 = some (AXPushParam.relocate 107 (AXPushParam.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p3 : resolveAt exactSites 135 = some (AXPushParam.relocate 107 (AXPushParam.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p4 : resolveAt exactSites 136 = some (AXPushParam.relocate 107 (AXPushParam.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p5 : resolveAt exactSites 137 = some (AXPushParam.relocate 107 (AXPushParam.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p6 : resolveAt exactSites 138 = some (AXPushParam.relocate 107 (AXPushParam.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p7 : resolveAt exactSites 139 = some (AXPushParam.relocate 107 (AXPushParam.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p8 : resolveAt exactSites 140 = some (AXPushParam.relocate 107 (AXPushParam.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p9 : resolveAt exactSites 141 = some (AXPushParam.relocate 107 (AXPushParam.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p10 : resolveAt exactSites 142 = some (AXPushParam.relocate 107 (AXPushParam.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p11 : resolveAt exactSites 143 = some (AXPushParam.relocate 107 (AXPushParam.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p12 : resolveAt exactSites 144 = some (AXPushParam.relocate 107 (AXPushParam.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p13 : resolveAt exactSites 145 = some (AXPushParam.relocate 107 (AXPushParam.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p14 : resolveAt exactSites 146 = some (AXPushParam.relocate 107 (AXPushParam.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p15 : resolveAt exactSites 147 = some (AXPushParam.relocate 107 (AXPushParam.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p16 : resolveAt exactSites 148 = some (AXPushParam.relocate 107 (AXPushParam.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p17 : resolveAt exactSites 149 = some (AXPushParam.relocate 107 (AXPushParam.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row132_p18 : resolveAt exactSites 150 = some (AXPushParam.relocate 107 (AXPushParam.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound132_p : AXPushParam.Bound exactSites 107 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row132_p0
  · exact row132_p1
  · exact row132_p2
  · exact row132_p3
  · exact row132_p4
  · exact row132_p5
  · exact row132_p6
  · exact row132_p7
  · exact row132_p8
  · exact row132_p9
  · exact row132_p10
  · exact row132_p11
  · exact row132_p12
  · exact row132_p13
  · exact row132_p14
  · exact row132_p15
  · exact row132_p16
  · exact row132_p17
  · exact row132_p18
theorem block132 : AXMacro.Realizes exactSites .push 132 151 :=
  AXMacro.push_realizes bound132_p
private theorem row151_c0 : resolveAt exactSites 151 = some (CopyToT.expected 4 151 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row151_c1 : resolveAt exactSites 152 = some (CopyToT.expected 4 151 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row151_c2 : resolveAt exactSites 153 = some (CopyToT.expected 4 151 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row151_c3 : resolveAt exactSites 154 = some (CopyToT.expected 4 151 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row151_c4 : resolveAt exactSites 155 = some (CopyToT.expected 4 151 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row151_c5 : resolveAt exactSites 156 = some (CopyToT.expected 4 151 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row151_c6 : resolveAt exactSites 157 = some (CopyToT.expected 4 151 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound151_c : CopyToT.Bound exactSites 4 151 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row151_c0
  · exact row151_c1
  · exact row151_c2
  · exact row151_c3
  · exact row151_c4
  · exact row151_c5
  · exact row151_c6
theorem block151 : AXMacro.Realizes exactSites .copyD 151 158 :=
  AXMacro.copyD_realizes bound151_c
private theorem row158_r0 : resolveAt exactSites 158 = some ((AXMacro.readerH 158).instruction unpairExpected[0]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row158_r1 : resolveAt exactSites 159 = some ((AXMacro.readerH 158).instruction unpairExpected[1]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row158_r2 : resolveAt exactSites 160 = some ((AXMacro.readerH 158).instruction unpairExpected[2]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row158_r3 : resolveAt exactSites 161 = some ((AXMacro.readerH 158).instruction unpairExpected[3]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row158_r4 : resolveAt exactSites 162 = some ((AXMacro.readerH 158).instruction unpairExpected[4]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row158_r5 : resolveAt exactSites 163 = some ((AXMacro.readerH 158).instruction unpairExpected[5]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row158_r6 : resolveAt exactSites 164 = some ((AXMacro.readerH 158).instruction unpairExpected[6]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row158_r7 : resolveAt exactSites 165 = some ((AXMacro.readerH 158).instruction unpairExpected[7]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row158_r8 : resolveAt exactSites 166 = some ((AXMacro.readerH 158).instruction unpairExpected[8]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row158_r9 : resolveAt exactSites 167 = some ((AXMacro.readerH 158).instruction unpairExpected[9]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row158_r10 : resolveAt exactSites 168 = some ((AXMacro.readerH 158).instruction unpairExpected[10]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row158_r11 : resolveAt exactSites 169 = some ((AXMacro.readerH 158).instruction unpairExpected[11]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row158_r12 : resolveAt exactSites 170 = some ((AXMacro.readerH 158).instruction unpairExpected[12]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row158_r13 : resolveAt exactSites 171 = some ((AXMacro.readerH 158).instruction unpairExpected[13]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound158_r : (AXMacro.readerH 158).Bound := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row158_r0
  · exact row158_r1
  · exact row158_r2
  · exact row158_r3
  · exact row158_r4
  · exact row158_r5
  · exact row158_r6
  · exact row158_r7
  · exact row158_r8
  · exact row158_r9
  · exact row158_r10
  · exact row158_r11
  · exact row158_r12
  · exact row158_r13
theorem block158 : AXMacro.Realizes exactSites .readH 158 172 :=
  AXMacro.readH_realizes 158 bound158_r
def code000 : List AXMacro.Op := [.push,.copyD,.push,.copyH,.cons,.incT,.incT,.push,.copyA,.push,.copyD,.readH]
theorem plan000 : AXMacro.Plan exactSites 25 172 code000 :=
  AXMacro.Plan.cons block25 ( AXMacro.Plan.cons block44 ( AXMacro.Plan.cons block51 ( AXMacro.Plan.cons block70 ( AXMacro.Plan.cons block77 ( AXMacro.Plan.cons block104 ( AXMacro.Plan.cons block105 ( AXMacro.Plan.cons block106 ( AXMacro.Plan.cons block125 ( AXMacro.Plan.cons block132 ( AXMacro.Plan.cons block151 ( AXMacro.Plan.cons block158 ( AXMacro.Plan.nil 172))))))))))))
#print axioms plan000
end M6.Source.AXAll

