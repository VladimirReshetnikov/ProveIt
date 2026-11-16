module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row1143_u0 : resolveAt exactSites 1143 = some (UnpairPartial.expected 1143 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_u1 : resolveAt exactSites 1144 = some (UnpairPartial.expected 1143 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_u2 : resolveAt exactSites 1145 = some (UnpairPartial.expected 1143 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_u3 : resolveAt exactSites 1146 = some (UnpairPartial.expected 1143 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_u4 : resolveAt exactSites 1147 = some (UnpairPartial.expected 1143 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_u5 : resolveAt exactSites 1148 = some (UnpairPartial.expected 1143 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_u6 : resolveAt exactSites 1149 = some (UnpairPartial.expected 1143 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_u7 : resolveAt exactSites 1150 = some (UnpairPartial.expected 1143 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_u8 : resolveAt exactSites 1151 = some (UnpairPartial.expected 1143 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_u9 : resolveAt exactSites 1152 = some (UnpairPartial.expected 1143 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_u10 : resolveAt exactSites 1153 = some (UnpairPartial.expected 1143 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1143_u : UnpairPartial.Bound exactSites 1143 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1143_u0
  · exact row1143_u1
  · exact row1143_u2
  · exact row1143_u3
  · exact row1143_u4
  · exact row1143_u5
  · exact row1143_u6
  · exact row1143_u7
  · exact row1143_u8
  · exact row1143_u9
  · exact row1143_u10
private theorem row1143_q0 : resolveAt exactSites 1154 = some (AXPair.relocate 1123 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_q1 : resolveAt exactSites 1155 = some (AXPair.relocate 1123 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_q2 : resolveAt exactSites 1156 = some (AXPair.relocate 1123 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_q3 : resolveAt exactSites 1157 = some (AXPair.relocate 1123 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_q4 : resolveAt exactSites 1158 = some (AXPair.relocate 1123 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_q5 : resolveAt exactSites 1159 = some (AXPair.relocate 1123 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_q6 : resolveAt exactSites 1160 = some (AXPair.relocate 1123 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_q7 : resolveAt exactSites 1161 = some (AXPair.relocate 1123 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_q8 : resolveAt exactSites 1162 = some (AXPair.relocate 1123 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_q9 : resolveAt exactSites 1163 = some (AXPair.relocate 1123 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1143_q : AXPair.Bound exactSites 1123 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1143_q0
  · exact row1143_q1
  · exact row1143_q2
  · exact row1143_q3
  · exact row1143_q4
  · exact row1143_q5
  · exact row1143_q6
  · exact row1143_q7
  · exact row1143_q8
  · exact row1143_q9
private theorem row1143_m0 : resolveAt exactSites 1164 = some (AXTimes4.expected 1164 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_m1 : resolveAt exactSites 1165 = some (AXTimes4.expected 1164 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_m2 : resolveAt exactSites 1166 = some (AXTimes4.expected 1164 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_m3 : resolveAt exactSites 1167 = some (AXTimes4.expected 1164 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_m4 : resolveAt exactSites 1168 = some (AXTimes4.expected 1164 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1143_m5 : resolveAt exactSites 1169 = some (AXTimes4.expected 1164 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1143_m : AXTimes4.Bound exactSites 1164 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1143_m0
  · exact row1143_m1
  · exact row1143_m2
  · exact row1143_m3
  · exact row1143_m4
  · exact row1143_m5
theorem block1143 : AXMacro.Realizes exactSites .cons 1143 1170 :=
  AXMacro.cons_realizes bound1143_u bound1143_q bound1143_m
private theorem row1170_p0 : resolveAt exactSites 1170 = some (AXPushParam.relocate 1145 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p1 : resolveAt exactSites 1171 = some (AXPushParam.relocate 1145 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p2 : resolveAt exactSites 1172 = some (AXPushParam.relocate 1145 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p3 : resolveAt exactSites 1173 = some (AXPushParam.relocate 1145 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p4 : resolveAt exactSites 1174 = some (AXPushParam.relocate 1145 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p5 : resolveAt exactSites 1175 = some (AXPushParam.relocate 1145 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p6 : resolveAt exactSites 1176 = some (AXPushParam.relocate 1145 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p7 : resolveAt exactSites 1177 = some (AXPushParam.relocate 1145 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p8 : resolveAt exactSites 1178 = some (AXPushParam.relocate 1145 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p9 : resolveAt exactSites 1179 = some (AXPushParam.relocate 1145 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p10 : resolveAt exactSites 1180 = some (AXPushParam.relocate 1145 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p11 : resolveAt exactSites 1181 = some (AXPushParam.relocate 1145 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p12 : resolveAt exactSites 1182 = some (AXPushParam.relocate 1145 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p13 : resolveAt exactSites 1183 = some (AXPushParam.relocate 1145 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p14 : resolveAt exactSites 1184 = some (AXPushParam.relocate 1145 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p15 : resolveAt exactSites 1185 = some (AXPushParam.relocate 1145 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p16 : resolveAt exactSites 1186 = some (AXPushParam.relocate 1145 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p17 : resolveAt exactSites 1187 = some (AXPushParam.relocate 1145 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1170_p18 : resolveAt exactSites 1188 = some (AXPushParam.relocate 1145 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1170_p : AXPushParam.Bound exactSites 1145 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1170_p0
  · exact row1170_p1
  · exact row1170_p2
  · exact row1170_p3
  · exact row1170_p4
  · exact row1170_p5
  · exact row1170_p6
  · exact row1170_p7
  · exact row1170_p8
  · exact row1170_p9
  · exact row1170_p10
  · exact row1170_p11
  · exact row1170_p12
  · exact row1170_p13
  · exact row1170_p14
  · exact row1170_p15
  · exact row1170_p16
  · exact row1170_p17
  · exact row1170_p18
theorem block1170 : AXMacro.Realizes exactSites .push 1170 1189 :=
  AXMacro.push_realizes bound1170_p
private theorem row1189_c0 : resolveAt exactSites 1189 = some (CopyToT.expected 3 1189 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1189_c1 : resolveAt exactSites 1190 = some (CopyToT.expected 3 1189 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1189_c2 : resolveAt exactSites 1191 = some (CopyToT.expected 3 1189 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1189_c3 : resolveAt exactSites 1192 = some (CopyToT.expected 3 1189 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1189_c4 : resolveAt exactSites 1193 = some (CopyToT.expected 3 1189 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1189_c5 : resolveAt exactSites 1194 = some (CopyToT.expected 3 1189 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1189_c6 : resolveAt exactSites 1195 = some (CopyToT.expected 3 1189 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1189_c : CopyToT.Bound exactSites 3 1189 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1189_c0
  · exact row1189_c1
  · exact row1189_c2
  · exact row1189_c3
  · exact row1189_c4
  · exact row1189_c5
  · exact row1189_c6
theorem block1189 : AXMacro.Realizes exactSites .copyA 1189 1196 :=
  AXMacro.copyA_realizes bound1189_c
private theorem row1196_p0 : resolveAt exactSites 1196 = some (AXPushParam.relocate 1171 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p1 : resolveAt exactSites 1197 = some (AXPushParam.relocate 1171 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p2 : resolveAt exactSites 1198 = some (AXPushParam.relocate 1171 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p3 : resolveAt exactSites 1199 = some (AXPushParam.relocate 1171 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p4 : resolveAt exactSites 1200 = some (AXPushParam.relocate 1171 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p5 : resolveAt exactSites 1201 = some (AXPushParam.relocate 1171 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p6 : resolveAt exactSites 1202 = some (AXPushParam.relocate 1171 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p7 : resolveAt exactSites 1203 = some (AXPushParam.relocate 1171 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p8 : resolveAt exactSites 1204 = some (AXPushParam.relocate 1171 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p9 : resolveAt exactSites 1205 = some (AXPushParam.relocate 1171 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p10 : resolveAt exactSites 1206 = some (AXPushParam.relocate 1171 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p11 : resolveAt exactSites 1207 = some (AXPushParam.relocate 1171 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p12 : resolveAt exactSites 1208 = some (AXPushParam.relocate 1171 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p13 : resolveAt exactSites 1209 = some (AXPushParam.relocate 1171 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p14 : resolveAt exactSites 1210 = some (AXPushParam.relocate 1171 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p15 : resolveAt exactSites 1211 = some (AXPushParam.relocate 1171 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p16 : resolveAt exactSites 1212 = some (AXPushParam.relocate 1171 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p17 : resolveAt exactSites 1213 = some (AXPushParam.relocate 1171 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1196_p18 : resolveAt exactSites 1214 = some (AXPushParam.relocate 1171 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1196_p : AXPushParam.Bound exactSites 1171 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1196_p0
  · exact row1196_p1
  · exact row1196_p2
  · exact row1196_p3
  · exact row1196_p4
  · exact row1196_p5
  · exact row1196_p6
  · exact row1196_p7
  · exact row1196_p8
  · exact row1196_p9
  · exact row1196_p10
  · exact row1196_p11
  · exact row1196_p12
  · exact row1196_p13
  · exact row1196_p14
  · exact row1196_p15
  · exact row1196_p16
  · exact row1196_p17
  · exact row1196_p18
theorem block1196 : AXMacro.Realizes exactSites .push 1196 1215 :=
  AXMacro.push_realizes bound1196_p
private theorem row1215_c0 : resolveAt exactSites 1215 = some (CopyToT.expected 4 1215 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1215_c1 : resolveAt exactSites 1216 = some (CopyToT.expected 4 1215 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1215_c2 : resolveAt exactSites 1217 = some (CopyToT.expected 4 1215 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1215_c3 : resolveAt exactSites 1218 = some (CopyToT.expected 4 1215 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1215_c4 : resolveAt exactSites 1219 = some (CopyToT.expected 4 1215 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1215_c5 : resolveAt exactSites 1220 = some (CopyToT.expected 4 1215 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1215_c6 : resolveAt exactSites 1221 = some (CopyToT.expected 4 1215 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1215_c : CopyToT.Bound exactSites 4 1215 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1215_c0
  · exact row1215_c1
  · exact row1215_c2
  · exact row1215_c3
  · exact row1215_c4
  · exact row1215_c5
  · exact row1215_c6
theorem block1215 : AXMacro.Realizes exactSites .copyD 1215 1222 :=
  AXMacro.copyD_realizes bound1215_c
private theorem row1222_u0 : resolveAt exactSites 1222 = some (UnpairPartial.expected 1222 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_u1 : resolveAt exactSites 1223 = some (UnpairPartial.expected 1222 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_u2 : resolveAt exactSites 1224 = some (UnpairPartial.expected 1222 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_u3 : resolveAt exactSites 1225 = some (UnpairPartial.expected 1222 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_u4 : resolveAt exactSites 1226 = some (UnpairPartial.expected 1222 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_u5 : resolveAt exactSites 1227 = some (UnpairPartial.expected 1222 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_u6 : resolveAt exactSites 1228 = some (UnpairPartial.expected 1222 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_u7 : resolveAt exactSites 1229 = some (UnpairPartial.expected 1222 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_u8 : resolveAt exactSites 1230 = some (UnpairPartial.expected 1222 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_u9 : resolveAt exactSites 1231 = some (UnpairPartial.expected 1222 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_u10 : resolveAt exactSites 1232 = some (UnpairPartial.expected 1222 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1222_u : UnpairPartial.Bound exactSites 1222 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1222_u0
  · exact row1222_u1
  · exact row1222_u2
  · exact row1222_u3
  · exact row1222_u4
  · exact row1222_u5
  · exact row1222_u6
  · exact row1222_u7
  · exact row1222_u8
  · exact row1222_u9
  · exact row1222_u10
private theorem row1222_q0 : resolveAt exactSites 1233 = some (AXPair.relocate 1202 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_q1 : resolveAt exactSites 1234 = some (AXPair.relocate 1202 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_q2 : resolveAt exactSites 1235 = some (AXPair.relocate 1202 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_q3 : resolveAt exactSites 1236 = some (AXPair.relocate 1202 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_q4 : resolveAt exactSites 1237 = some (AXPair.relocate 1202 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_q5 : resolveAt exactSites 1238 = some (AXPair.relocate 1202 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_q6 : resolveAt exactSites 1239 = some (AXPair.relocate 1202 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_q7 : resolveAt exactSites 1240 = some (AXPair.relocate 1202 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_q8 : resolveAt exactSites 1241 = some (AXPair.relocate 1202 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_q9 : resolveAt exactSites 1242 = some (AXPair.relocate 1202 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1222_q : AXPair.Bound exactSites 1202 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1222_q0
  · exact row1222_q1
  · exact row1222_q2
  · exact row1222_q3
  · exact row1222_q4
  · exact row1222_q5
  · exact row1222_q6
  · exact row1222_q7
  · exact row1222_q8
  · exact row1222_q9
private theorem row1222_m0 : resolveAt exactSites 1243 = some (AXTimes4.expected 1243 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_m1 : resolveAt exactSites 1244 = some (AXTimes4.expected 1243 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_m2 : resolveAt exactSites 1245 = some (AXTimes4.expected 1243 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_m3 : resolveAt exactSites 1246 = some (AXTimes4.expected 1243 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_m4 : resolveAt exactSites 1247 = some (AXTimes4.expected 1243 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1222_m5 : resolveAt exactSites 1248 = some (AXTimes4.expected 1243 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1222_m : AXTimes4.Bound exactSites 1243 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1222_m0
  · exact row1222_m1
  · exact row1222_m2
  · exact row1222_m3
  · exact row1222_m4
  · exact row1222_m5
theorem block1222 : AXMacro.Realizes exactSites .cons 1222 1249 :=
  AXMacro.cons_realizes bound1222_u bound1222_q bound1222_m
private theorem row1249_i0 : resolveAt exactSites 1249 = some (Instruction.inc 1 (some 1250)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block1249 : AXMacro.Realizes exactSites .incT 1249 1250 :=
  AXMacro.inc_realizes row1249_i0
private theorem row1250_i0 : resolveAt exactSites 1250 = some (Instruction.inc 1 (some 1251)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block1250 : AXMacro.Realizes exactSites .incT 1250 1251 :=
  AXMacro.inc_realizes row1250_i0
private theorem row1251_i0 : resolveAt exactSites 1251 = some (Instruction.inc 1 (some 1252)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block1251 : AXMacro.Realizes exactSites .incT 1251 1252 :=
  AXMacro.inc_realizes row1251_i0
private theorem row1252_p0 : resolveAt exactSites 1252 = some (AXPushParam.relocate 1227 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p1 : resolveAt exactSites 1253 = some (AXPushParam.relocate 1227 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p2 : resolveAt exactSites 1254 = some (AXPushParam.relocate 1227 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p3 : resolveAt exactSites 1255 = some (AXPushParam.relocate 1227 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p4 : resolveAt exactSites 1256 = some (AXPushParam.relocate 1227 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p5 : resolveAt exactSites 1257 = some (AXPushParam.relocate 1227 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p6 : resolveAt exactSites 1258 = some (AXPushParam.relocate 1227 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p7 : resolveAt exactSites 1259 = some (AXPushParam.relocate 1227 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p8 : resolveAt exactSites 1260 = some (AXPushParam.relocate 1227 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p9 : resolveAt exactSites 1261 = some (AXPushParam.relocate 1227 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p10 : resolveAt exactSites 1262 = some (AXPushParam.relocate 1227 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p11 : resolveAt exactSites 1263 = some (AXPushParam.relocate 1227 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p12 : resolveAt exactSites 1264 = some (AXPushParam.relocate 1227 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p13 : resolveAt exactSites 1265 = some (AXPushParam.relocate 1227 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p14 : resolveAt exactSites 1266 = some (AXPushParam.relocate 1227 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p15 : resolveAt exactSites 1267 = some (AXPushParam.relocate 1227 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p16 : resolveAt exactSites 1268 = some (AXPushParam.relocate 1227 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p17 : resolveAt exactSites 1269 = some (AXPushParam.relocate 1227 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1252_p18 : resolveAt exactSites 1270 = some (AXPushParam.relocate 1227 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1252_p : AXPushParam.Bound exactSites 1227 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1252_p0
  · exact row1252_p1
  · exact row1252_p2
  · exact row1252_p3
  · exact row1252_p4
  · exact row1252_p5
  · exact row1252_p6
  · exact row1252_p7
  · exact row1252_p8
  · exact row1252_p9
  · exact row1252_p10
  · exact row1252_p11
  · exact row1252_p12
  · exact row1252_p13
  · exact row1252_p14
  · exact row1252_p15
  · exact row1252_p16
  · exact row1252_p17
  · exact row1252_p18
theorem block1252 : AXMacro.Realizes exactSites .push 1252 1271 :=
  AXMacro.push_realizes bound1252_p
private theorem row1271_c0 : resolveAt exactSites 1271 = some (CopyToT.expected 3 1271 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1271_c1 : resolveAt exactSites 1272 = some (CopyToT.expected 3 1271 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1271_c2 : resolveAt exactSites 1273 = some (CopyToT.expected 3 1271 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1271_c3 : resolveAt exactSites 1274 = some (CopyToT.expected 3 1271 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1271_c4 : resolveAt exactSites 1275 = some (CopyToT.expected 3 1271 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1271_c5 : resolveAt exactSites 1276 = some (CopyToT.expected 3 1271 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1271_c6 : resolveAt exactSites 1277 = some (CopyToT.expected 3 1271 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1271_c : CopyToT.Bound exactSites 3 1271 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1271_c0
  · exact row1271_c1
  · exact row1271_c2
  · exact row1271_c3
  · exact row1271_c4
  · exact row1271_c5
  · exact row1271_c6
theorem block1271 : AXMacro.Realizes exactSites .copyA 1271 1278 :=
  AXMacro.copyA_realizes bound1271_c
private theorem row1278_p0 : resolveAt exactSites 1278 = some (AXPushParam.relocate 1253 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p1 : resolveAt exactSites 1279 = some (AXPushParam.relocate 1253 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p2 : resolveAt exactSites 1280 = some (AXPushParam.relocate 1253 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p3 : resolveAt exactSites 1281 = some (AXPushParam.relocate 1253 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p4 : resolveAt exactSites 1282 = some (AXPushParam.relocate 1253 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p5 : resolveAt exactSites 1283 = some (AXPushParam.relocate 1253 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p6 : resolveAt exactSites 1284 = some (AXPushParam.relocate 1253 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p7 : resolveAt exactSites 1285 = some (AXPushParam.relocate 1253 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p8 : resolveAt exactSites 1286 = some (AXPushParam.relocate 1253 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p9 : resolveAt exactSites 1287 = some (AXPushParam.relocate 1253 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p10 : resolveAt exactSites 1288 = some (AXPushParam.relocate 1253 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p11 : resolveAt exactSites 1289 = some (AXPushParam.relocate 1253 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p12 : resolveAt exactSites 1290 = some (AXPushParam.relocate 1253 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p13 : resolveAt exactSites 1291 = some (AXPushParam.relocate 1253 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p14 : resolveAt exactSites 1292 = some (AXPushParam.relocate 1253 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p15 : resolveAt exactSites 1293 = some (AXPushParam.relocate 1253 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p16 : resolveAt exactSites 1294 = some (AXPushParam.relocate 1253 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p17 : resolveAt exactSites 1295 = some (AXPushParam.relocate 1253 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1278_p18 : resolveAt exactSites 1296 = some (AXPushParam.relocate 1253 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1278_p : AXPushParam.Bound exactSites 1253 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1278_p0
  · exact row1278_p1
  · exact row1278_p2
  · exact row1278_p3
  · exact row1278_p4
  · exact row1278_p5
  · exact row1278_p6
  · exact row1278_p7
  · exact row1278_p8
  · exact row1278_p9
  · exact row1278_p10
  · exact row1278_p11
  · exact row1278_p12
  · exact row1278_p13
  · exact row1278_p14
  · exact row1278_p15
  · exact row1278_p16
  · exact row1278_p17
  · exact row1278_p18
theorem block1278 : AXMacro.Realizes exactSites .push 1278 1297 :=
  AXMacro.push_realizes bound1278_p
def code007 : List AXMacro.Op := [.cons,.push,.copyA,.push,.copyD,.cons,.incT,.incT,.incT,.push,.copyA,.push]
theorem plan007 : AXMacro.Plan exactSites 1143 1297 code007 :=
  AXMacro.Plan.cons block1143 ( AXMacro.Plan.cons block1170 ( AXMacro.Plan.cons block1189 ( AXMacro.Plan.cons block1196 ( AXMacro.Plan.cons block1215 ( AXMacro.Plan.cons block1222 ( AXMacro.Plan.cons block1249 ( AXMacro.Plan.cons block1250 ( AXMacro.Plan.cons block1251 ( AXMacro.Plan.cons block1252 ( AXMacro.Plan.cons block1271 ( AXMacro.Plan.cons block1278 ( AXMacro.Plan.nil 1297))))))))))))
#print axioms plan007
end M6.Source.AXAll

