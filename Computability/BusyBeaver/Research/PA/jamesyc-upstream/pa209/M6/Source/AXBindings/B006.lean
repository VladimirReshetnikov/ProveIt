module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row993_i0 : resolveAt exactSites 993 = some (Instruction.inc 1 (some 994)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block993 : AXMacro.Realizes exactSites .incT 993 994 :=
  AXMacro.inc_realizes row993_i0
private theorem row994_p0 : resolveAt exactSites 994 = some (AXPushParam.relocate 969 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p1 : resolveAt exactSites 995 = some (AXPushParam.relocate 969 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p2 : resolveAt exactSites 996 = some (AXPushParam.relocate 969 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p3 : resolveAt exactSites 997 = some (AXPushParam.relocate 969 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p4 : resolveAt exactSites 998 = some (AXPushParam.relocate 969 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p5 : resolveAt exactSites 999 = some (AXPushParam.relocate 969 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p6 : resolveAt exactSites 1000 = some (AXPushParam.relocate 969 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p7 : resolveAt exactSites 1001 = some (AXPushParam.relocate 969 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p8 : resolveAt exactSites 1002 = some (AXPushParam.relocate 969 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p9 : resolveAt exactSites 1003 = some (AXPushParam.relocate 969 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p10 : resolveAt exactSites 1004 = some (AXPushParam.relocate 969 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p11 : resolveAt exactSites 1005 = some (AXPushParam.relocate 969 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p12 : resolveAt exactSites 1006 = some (AXPushParam.relocate 969 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p13 : resolveAt exactSites 1007 = some (AXPushParam.relocate 969 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p14 : resolveAt exactSites 1008 = some (AXPushParam.relocate 969 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p15 : resolveAt exactSites 1009 = some (AXPushParam.relocate 969 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p16 : resolveAt exactSites 1010 = some (AXPushParam.relocate 969 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p17 : resolveAt exactSites 1011 = some (AXPushParam.relocate 969 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row994_p18 : resolveAt exactSites 1012 = some (AXPushParam.relocate 969 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound994_p : AXPushParam.Bound exactSites 969 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row994_p0
  · exact row994_p1
  · exact row994_p2
  · exact row994_p3
  · exact row994_p4
  · exact row994_p5
  · exact row994_p6
  · exact row994_p7
  · exact row994_p8
  · exact row994_p9
  · exact row994_p10
  · exact row994_p11
  · exact row994_p12
  · exact row994_p13
  · exact row994_p14
  · exact row994_p15
  · exact row994_p16
  · exact row994_p17
  · exact row994_p18
theorem block994 : AXMacro.Realizes exactSites .push 994 1013 :=
  AXMacro.push_realizes bound994_p
private theorem row1013_i0 : resolveAt exactSites 1013 = some (Instruction.inc 1 (some 1014)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block1013 : AXMacro.Realizes exactSites .incT 1013 1014 :=
  AXMacro.inc_realizes row1013_i0
private theorem row1014_u0 : resolveAt exactSites 1014 = some (UnpairPartial.expected 1014 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_u1 : resolveAt exactSites 1015 = some (UnpairPartial.expected 1014 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_u2 : resolveAt exactSites 1016 = some (UnpairPartial.expected 1014 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_u3 : resolveAt exactSites 1017 = some (UnpairPartial.expected 1014 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_u4 : resolveAt exactSites 1018 = some (UnpairPartial.expected 1014 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_u5 : resolveAt exactSites 1019 = some (UnpairPartial.expected 1014 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_u6 : resolveAt exactSites 1020 = some (UnpairPartial.expected 1014 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_u7 : resolveAt exactSites 1021 = some (UnpairPartial.expected 1014 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_u8 : resolveAt exactSites 1022 = some (UnpairPartial.expected 1014 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_u9 : resolveAt exactSites 1023 = some (UnpairPartial.expected 1014 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_u10 : resolveAt exactSites 1024 = some (UnpairPartial.expected 1014 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1014_u : UnpairPartial.Bound exactSites 1014 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1014_u0
  · exact row1014_u1
  · exact row1014_u2
  · exact row1014_u3
  · exact row1014_u4
  · exact row1014_u5
  · exact row1014_u6
  · exact row1014_u7
  · exact row1014_u8
  · exact row1014_u9
  · exact row1014_u10
private theorem row1014_q0 : resolveAt exactSites 1025 = some (AXPair.relocate 994 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_q1 : resolveAt exactSites 1026 = some (AXPair.relocate 994 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_q2 : resolveAt exactSites 1027 = some (AXPair.relocate 994 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_q3 : resolveAt exactSites 1028 = some (AXPair.relocate 994 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_q4 : resolveAt exactSites 1029 = some (AXPair.relocate 994 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_q5 : resolveAt exactSites 1030 = some (AXPair.relocate 994 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_q6 : resolveAt exactSites 1031 = some (AXPair.relocate 994 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_q7 : resolveAt exactSites 1032 = some (AXPair.relocate 994 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_q8 : resolveAt exactSites 1033 = some (AXPair.relocate 994 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_q9 : resolveAt exactSites 1034 = some (AXPair.relocate 994 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1014_q : AXPair.Bound exactSites 994 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1014_q0
  · exact row1014_q1
  · exact row1014_q2
  · exact row1014_q3
  · exact row1014_q4
  · exact row1014_q5
  · exact row1014_q6
  · exact row1014_q7
  · exact row1014_q8
  · exact row1014_q9
private theorem row1014_m0 : resolveAt exactSites 1035 = some (AXTimes4.expected 1035 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_m1 : resolveAt exactSites 1036 = some (AXTimes4.expected 1035 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_m2 : resolveAt exactSites 1037 = some (AXTimes4.expected 1035 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_m3 : resolveAt exactSites 1038 = some (AXTimes4.expected 1035 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_m4 : resolveAt exactSites 1039 = some (AXTimes4.expected 1035 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1014_m5 : resolveAt exactSites 1040 = some (AXTimes4.expected 1035 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1014_m : AXTimes4.Bound exactSites 1035 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1014_m0
  · exact row1014_m1
  · exact row1014_m2
  · exact row1014_m3
  · exact row1014_m4
  · exact row1014_m5
theorem block1014 : AXMacro.Realizes exactSites .cons 1014 1041 :=
  AXMacro.cons_realizes bound1014_u bound1014_q bound1014_m
private theorem row1041_u0 : resolveAt exactSites 1041 = some (UnpairPartial.expected 1041 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_u1 : resolveAt exactSites 1042 = some (UnpairPartial.expected 1041 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_u2 : resolveAt exactSites 1043 = some (UnpairPartial.expected 1041 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_u3 : resolveAt exactSites 1044 = some (UnpairPartial.expected 1041 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_u4 : resolveAt exactSites 1045 = some (UnpairPartial.expected 1041 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_u5 : resolveAt exactSites 1046 = some (UnpairPartial.expected 1041 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_u6 : resolveAt exactSites 1047 = some (UnpairPartial.expected 1041 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_u7 : resolveAt exactSites 1048 = some (UnpairPartial.expected 1041 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_u8 : resolveAt exactSites 1049 = some (UnpairPartial.expected 1041 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_u9 : resolveAt exactSites 1050 = some (UnpairPartial.expected 1041 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_u10 : resolveAt exactSites 1051 = some (UnpairPartial.expected 1041 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1041_u : UnpairPartial.Bound exactSites 1041 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1041_u0
  · exact row1041_u1
  · exact row1041_u2
  · exact row1041_u3
  · exact row1041_u4
  · exact row1041_u5
  · exact row1041_u6
  · exact row1041_u7
  · exact row1041_u8
  · exact row1041_u9
  · exact row1041_u10
private theorem row1041_q0 : resolveAt exactSites 1052 = some (AXPair.relocate 1021 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_q1 : resolveAt exactSites 1053 = some (AXPair.relocate 1021 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_q2 : resolveAt exactSites 1054 = some (AXPair.relocate 1021 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_q3 : resolveAt exactSites 1055 = some (AXPair.relocate 1021 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_q4 : resolveAt exactSites 1056 = some (AXPair.relocate 1021 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_q5 : resolveAt exactSites 1057 = some (AXPair.relocate 1021 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_q6 : resolveAt exactSites 1058 = some (AXPair.relocate 1021 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_q7 : resolveAt exactSites 1059 = some (AXPair.relocate 1021 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_q8 : resolveAt exactSites 1060 = some (AXPair.relocate 1021 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_q9 : resolveAt exactSites 1061 = some (AXPair.relocate 1021 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1041_q : AXPair.Bound exactSites 1021 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1041_q0
  · exact row1041_q1
  · exact row1041_q2
  · exact row1041_q3
  · exact row1041_q4
  · exact row1041_q5
  · exact row1041_q6
  · exact row1041_q7
  · exact row1041_q8
  · exact row1041_q9
private theorem row1041_m0 : resolveAt exactSites 1062 = some (AXTimes4.expected 1062 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_m1 : resolveAt exactSites 1063 = some (AXTimes4.expected 1062 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_m2 : resolveAt exactSites 1064 = some (AXTimes4.expected 1062 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_m3 : resolveAt exactSites 1065 = some (AXTimes4.expected 1062 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_m4 : resolveAt exactSites 1066 = some (AXTimes4.expected 1062 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1041_m5 : resolveAt exactSites 1067 = some (AXTimes4.expected 1062 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1041_m : AXTimes4.Bound exactSites 1062 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1041_m0
  · exact row1041_m1
  · exact row1041_m2
  · exact row1041_m3
  · exact row1041_m4
  · exact row1041_m5
theorem block1041 : AXMacro.Realizes exactSites .cons 1041 1068 :=
  AXMacro.cons_realizes bound1041_u bound1041_q bound1041_m
private theorem row1068_i0 : resolveAt exactSites 1068 = some (Instruction.inc 1 (some 1069)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block1068 : AXMacro.Realizes exactSites .incT 1068 1069 :=
  AXMacro.inc_realizes row1068_i0
private theorem row1069_i0 : resolveAt exactSites 1069 = some (Instruction.inc 1 (some 1070)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block1069 : AXMacro.Realizes exactSites .incT 1069 1070 :=
  AXMacro.inc_realizes row1069_i0
private theorem row1070_p0 : resolveAt exactSites 1070 = some (AXPushParam.relocate 1045 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p1 : resolveAt exactSites 1071 = some (AXPushParam.relocate 1045 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p2 : resolveAt exactSites 1072 = some (AXPushParam.relocate 1045 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p3 : resolveAt exactSites 1073 = some (AXPushParam.relocate 1045 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p4 : resolveAt exactSites 1074 = some (AXPushParam.relocate 1045 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p5 : resolveAt exactSites 1075 = some (AXPushParam.relocate 1045 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p6 : resolveAt exactSites 1076 = some (AXPushParam.relocate 1045 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p7 : resolveAt exactSites 1077 = some (AXPushParam.relocate 1045 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p8 : resolveAt exactSites 1078 = some (AXPushParam.relocate 1045 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p9 : resolveAt exactSites 1079 = some (AXPushParam.relocate 1045 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p10 : resolveAt exactSites 1080 = some (AXPushParam.relocate 1045 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p11 : resolveAt exactSites 1081 = some (AXPushParam.relocate 1045 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p12 : resolveAt exactSites 1082 = some (AXPushParam.relocate 1045 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p13 : resolveAt exactSites 1083 = some (AXPushParam.relocate 1045 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p14 : resolveAt exactSites 1084 = some (AXPushParam.relocate 1045 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p15 : resolveAt exactSites 1085 = some (AXPushParam.relocate 1045 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p16 : resolveAt exactSites 1086 = some (AXPushParam.relocate 1045 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p17 : resolveAt exactSites 1087 = some (AXPushParam.relocate 1045 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1070_p18 : resolveAt exactSites 1088 = some (AXPushParam.relocate 1045 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1070_p : AXPushParam.Bound exactSites 1045 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1070_p0
  · exact row1070_p1
  · exact row1070_p2
  · exact row1070_p3
  · exact row1070_p4
  · exact row1070_p5
  · exact row1070_p6
  · exact row1070_p7
  · exact row1070_p8
  · exact row1070_p9
  · exact row1070_p10
  · exact row1070_p11
  · exact row1070_p12
  · exact row1070_p13
  · exact row1070_p14
  · exact row1070_p15
  · exact row1070_p16
  · exact row1070_p17
  · exact row1070_p18
theorem block1070 : AXMacro.Realizes exactSites .push 1070 1089 :=
  AXMacro.push_realizes bound1070_p
private theorem row1089_i0 : resolveAt exactSites 1089 = some (Instruction.inc 1 (some 1090)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block1089 : AXMacro.Realizes exactSites .incT 1089 1090 :=
  AXMacro.inc_realizes row1089_i0
private theorem row1090_u0 : resolveAt exactSites 1090 = some (UnpairPartial.expected 1090 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_u1 : resolveAt exactSites 1091 = some (UnpairPartial.expected 1090 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_u2 : resolveAt exactSites 1092 = some (UnpairPartial.expected 1090 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_u3 : resolveAt exactSites 1093 = some (UnpairPartial.expected 1090 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_u4 : resolveAt exactSites 1094 = some (UnpairPartial.expected 1090 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_u5 : resolveAt exactSites 1095 = some (UnpairPartial.expected 1090 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_u6 : resolveAt exactSites 1096 = some (UnpairPartial.expected 1090 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_u7 : resolveAt exactSites 1097 = some (UnpairPartial.expected 1090 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_u8 : resolveAt exactSites 1098 = some (UnpairPartial.expected 1090 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_u9 : resolveAt exactSites 1099 = some (UnpairPartial.expected 1090 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_u10 : resolveAt exactSites 1100 = some (UnpairPartial.expected 1090 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1090_u : UnpairPartial.Bound exactSites 1090 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1090_u0
  · exact row1090_u1
  · exact row1090_u2
  · exact row1090_u3
  · exact row1090_u4
  · exact row1090_u5
  · exact row1090_u6
  · exact row1090_u7
  · exact row1090_u8
  · exact row1090_u9
  · exact row1090_u10
private theorem row1090_q0 : resolveAt exactSites 1101 = some (AXPair.relocate 1070 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_q1 : resolveAt exactSites 1102 = some (AXPair.relocate 1070 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_q2 : resolveAt exactSites 1103 = some (AXPair.relocate 1070 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_q3 : resolveAt exactSites 1104 = some (AXPair.relocate 1070 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_q4 : resolveAt exactSites 1105 = some (AXPair.relocate 1070 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_q5 : resolveAt exactSites 1106 = some (AXPair.relocate 1070 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_q6 : resolveAt exactSites 1107 = some (AXPair.relocate 1070 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_q7 : resolveAt exactSites 1108 = some (AXPair.relocate 1070 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_q8 : resolveAt exactSites 1109 = some (AXPair.relocate 1070 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_q9 : resolveAt exactSites 1110 = some (AXPair.relocate 1070 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1090_q : AXPair.Bound exactSites 1070 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1090_q0
  · exact row1090_q1
  · exact row1090_q2
  · exact row1090_q3
  · exact row1090_q4
  · exact row1090_q5
  · exact row1090_q6
  · exact row1090_q7
  · exact row1090_q8
  · exact row1090_q9
private theorem row1090_m0 : resolveAt exactSites 1111 = some (AXTimes4.expected 1111 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_m1 : resolveAt exactSites 1112 = some (AXTimes4.expected 1111 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_m2 : resolveAt exactSites 1113 = some (AXTimes4.expected 1111 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_m3 : resolveAt exactSites 1114 = some (AXTimes4.expected 1111 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_m4 : resolveAt exactSites 1115 = some (AXTimes4.expected 1111 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1090_m5 : resolveAt exactSites 1116 = some (AXTimes4.expected 1111 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1090_m : AXTimes4.Bound exactSites 1111 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1090_m0
  · exact row1090_m1
  · exact row1090_m2
  · exact row1090_m3
  · exact row1090_m4
  · exact row1090_m5
theorem block1090 : AXMacro.Realizes exactSites .cons 1090 1117 :=
  AXMacro.cons_realizes bound1090_u bound1090_q bound1090_m
private theorem row1117_p0 : resolveAt exactSites 1117 = some (AXPushParam.relocate 1092 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p1 : resolveAt exactSites 1118 = some (AXPushParam.relocate 1092 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p2 : resolveAt exactSites 1119 = some (AXPushParam.relocate 1092 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p3 : resolveAt exactSites 1120 = some (AXPushParam.relocate 1092 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p4 : resolveAt exactSites 1121 = some (AXPushParam.relocate 1092 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p5 : resolveAt exactSites 1122 = some (AXPushParam.relocate 1092 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p6 : resolveAt exactSites 1123 = some (AXPushParam.relocate 1092 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p7 : resolveAt exactSites 1124 = some (AXPushParam.relocate 1092 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p8 : resolveAt exactSites 1125 = some (AXPushParam.relocate 1092 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p9 : resolveAt exactSites 1126 = some (AXPushParam.relocate 1092 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p10 : resolveAt exactSites 1127 = some (AXPushParam.relocate 1092 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p11 : resolveAt exactSites 1128 = some (AXPushParam.relocate 1092 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p12 : resolveAt exactSites 1129 = some (AXPushParam.relocate 1092 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p13 : resolveAt exactSites 1130 = some (AXPushParam.relocate 1092 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p14 : resolveAt exactSites 1131 = some (AXPushParam.relocate 1092 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p15 : resolveAt exactSites 1132 = some (AXPushParam.relocate 1092 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p16 : resolveAt exactSites 1133 = some (AXPushParam.relocate 1092 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p17 : resolveAt exactSites 1134 = some (AXPushParam.relocate 1092 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1117_p18 : resolveAt exactSites 1135 = some (AXPushParam.relocate 1092 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1117_p : AXPushParam.Bound exactSites 1092 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1117_p0
  · exact row1117_p1
  · exact row1117_p2
  · exact row1117_p3
  · exact row1117_p4
  · exact row1117_p5
  · exact row1117_p6
  · exact row1117_p7
  · exact row1117_p8
  · exact row1117_p9
  · exact row1117_p10
  · exact row1117_p11
  · exact row1117_p12
  · exact row1117_p13
  · exact row1117_p14
  · exact row1117_p15
  · exact row1117_p16
  · exact row1117_p17
  · exact row1117_p18
theorem block1117 : AXMacro.Realizes exactSites .push 1117 1136 :=
  AXMacro.push_realizes bound1117_p
private theorem row1136_c0 : resolveAt exactSites 1136 = some (CopyToT.expected 5 1136 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1136_c1 : resolveAt exactSites 1137 = some (CopyToT.expected 5 1136 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1136_c2 : resolveAt exactSites 1138 = some (CopyToT.expected 5 1136 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1136_c3 : resolveAt exactSites 1139 = some (CopyToT.expected 5 1136 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1136_c4 : resolveAt exactSites 1140 = some (CopyToT.expected 5 1136 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1136_c5 : resolveAt exactSites 1141 = some (CopyToT.expected 5 1136 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1136_c6 : resolveAt exactSites 1142 = some (CopyToT.expected 5 1136 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1136_c : CopyToT.Bound exactSites 5 1136 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1136_c0
  · exact row1136_c1
  · exact row1136_c2
  · exact row1136_c3
  · exact row1136_c4
  · exact row1136_c5
  · exact row1136_c6
theorem block1136 : AXMacro.Realizes exactSites .copyH 1136 1143 :=
  AXMacro.copyH_realizes bound1136_c
def code006 : List AXMacro.Op := [.incT,.push,.incT,.cons,.cons,.incT,.incT,.push,.incT,.cons,.push,.copyH]
theorem plan006 : AXMacro.Plan exactSites 993 1143 code006 :=
  AXMacro.Plan.cons block993 ( AXMacro.Plan.cons block994 ( AXMacro.Plan.cons block1013 ( AXMacro.Plan.cons block1014 ( AXMacro.Plan.cons block1041 ( AXMacro.Plan.cons block1068 ( AXMacro.Plan.cons block1069 ( AXMacro.Plan.cons block1070 ( AXMacro.Plan.cons block1089 ( AXMacro.Plan.cons block1090 ( AXMacro.Plan.cons block1117 ( AXMacro.Plan.cons block1136 ( AXMacro.Plan.nil 1143))))))))))))
#print axioms plan006
end M6.Source.AXAll

