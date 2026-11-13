module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row1297_c0 : resolveAt exactSites 1297 = some (CopyToT.expected 5 1297 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1297_c1 : resolveAt exactSites 1298 = some (CopyToT.expected 5 1297 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1297_c2 : resolveAt exactSites 1299 = some (CopyToT.expected 5 1297 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1297_c3 : resolveAt exactSites 1300 = some (CopyToT.expected 5 1297 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1297_c4 : resolveAt exactSites 1301 = some (CopyToT.expected 5 1297 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1297_c5 : resolveAt exactSites 1302 = some (CopyToT.expected 5 1297 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1297_c6 : resolveAt exactSites 1303 = some (CopyToT.expected 5 1297 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1297_c : CopyToT.Bound exactSites 5 1297 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1297_c0
  · exact row1297_c1
  · exact row1297_c2
  · exact row1297_c3
  · exact row1297_c4
  · exact row1297_c5
  · exact row1297_c6
theorem block1297 : AXMacro.Realizes exactSites .copyH 1297 1304 :=
  AXMacro.copyH_realizes bound1297_c
private theorem row1304_u0 : resolveAt exactSites 1304 = some (UnpairPartial.expected 1304 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_u1 : resolveAt exactSites 1305 = some (UnpairPartial.expected 1304 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_u2 : resolveAt exactSites 1306 = some (UnpairPartial.expected 1304 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_u3 : resolveAt exactSites 1307 = some (UnpairPartial.expected 1304 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_u4 : resolveAt exactSites 1308 = some (UnpairPartial.expected 1304 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_u5 : resolveAt exactSites 1309 = some (UnpairPartial.expected 1304 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_u6 : resolveAt exactSites 1310 = some (UnpairPartial.expected 1304 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_u7 : resolveAt exactSites 1311 = some (UnpairPartial.expected 1304 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_u8 : resolveAt exactSites 1312 = some (UnpairPartial.expected 1304 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_u9 : resolveAt exactSites 1313 = some (UnpairPartial.expected 1304 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_u10 : resolveAt exactSites 1314 = some (UnpairPartial.expected 1304 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1304_u : UnpairPartial.Bound exactSites 1304 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1304_u0
  · exact row1304_u1
  · exact row1304_u2
  · exact row1304_u3
  · exact row1304_u4
  · exact row1304_u5
  · exact row1304_u6
  · exact row1304_u7
  · exact row1304_u8
  · exact row1304_u9
  · exact row1304_u10
private theorem row1304_q0 : resolveAt exactSites 1315 = some (AXPair.relocate 1284 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_q1 : resolveAt exactSites 1316 = some (AXPair.relocate 1284 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_q2 : resolveAt exactSites 1317 = some (AXPair.relocate 1284 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_q3 : resolveAt exactSites 1318 = some (AXPair.relocate 1284 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_q4 : resolveAt exactSites 1319 = some (AXPair.relocate 1284 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_q5 : resolveAt exactSites 1320 = some (AXPair.relocate 1284 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_q6 : resolveAt exactSites 1321 = some (AXPair.relocate 1284 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_q7 : resolveAt exactSites 1322 = some (AXPair.relocate 1284 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_q8 : resolveAt exactSites 1323 = some (AXPair.relocate 1284 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_q9 : resolveAt exactSites 1324 = some (AXPair.relocate 1284 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1304_q : AXPair.Bound exactSites 1284 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1304_q0
  · exact row1304_q1
  · exact row1304_q2
  · exact row1304_q3
  · exact row1304_q4
  · exact row1304_q5
  · exact row1304_q6
  · exact row1304_q7
  · exact row1304_q8
  · exact row1304_q9
private theorem row1304_m0 : resolveAt exactSites 1325 = some (AXTimes4.expected 1325 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_m1 : resolveAt exactSites 1326 = some (AXTimes4.expected 1325 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_m2 : resolveAt exactSites 1327 = some (AXTimes4.expected 1325 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_m3 : resolveAt exactSites 1328 = some (AXTimes4.expected 1325 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_m4 : resolveAt exactSites 1329 = some (AXTimes4.expected 1325 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1304_m5 : resolveAt exactSites 1330 = some (AXTimes4.expected 1325 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1304_m : AXTimes4.Bound exactSites 1325 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1304_m0
  · exact row1304_m1
  · exact row1304_m2
  · exact row1304_m3
  · exact row1304_m4
  · exact row1304_m5
theorem block1304 : AXMacro.Realizes exactSites .cons 1304 1331 :=
  AXMacro.cons_realizes bound1304_u bound1304_q bound1304_m
private theorem row1331_i0 : resolveAt exactSites 1331 = some (Instruction.inc 1 (some 1332)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block1331 : AXMacro.Realizes exactSites .incT 1331 1332 :=
  AXMacro.inc_realizes row1331_i0
private theorem row1332_p0 : resolveAt exactSites 1332 = some (AXPushParam.relocate 1307 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p1 : resolveAt exactSites 1333 = some (AXPushParam.relocate 1307 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p2 : resolveAt exactSites 1334 = some (AXPushParam.relocate 1307 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p3 : resolveAt exactSites 1335 = some (AXPushParam.relocate 1307 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p4 : resolveAt exactSites 1336 = some (AXPushParam.relocate 1307 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p5 : resolveAt exactSites 1337 = some (AXPushParam.relocate 1307 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p6 : resolveAt exactSites 1338 = some (AXPushParam.relocate 1307 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p7 : resolveAt exactSites 1339 = some (AXPushParam.relocate 1307 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p8 : resolveAt exactSites 1340 = some (AXPushParam.relocate 1307 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p9 : resolveAt exactSites 1341 = some (AXPushParam.relocate 1307 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p10 : resolveAt exactSites 1342 = some (AXPushParam.relocate 1307 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p11 : resolveAt exactSites 1343 = some (AXPushParam.relocate 1307 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p12 : resolveAt exactSites 1344 = some (AXPushParam.relocate 1307 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p13 : resolveAt exactSites 1345 = some (AXPushParam.relocate 1307 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p14 : resolveAt exactSites 1346 = some (AXPushParam.relocate 1307 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p15 : resolveAt exactSites 1347 = some (AXPushParam.relocate 1307 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p16 : resolveAt exactSites 1348 = some (AXPushParam.relocate 1307 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p17 : resolveAt exactSites 1349 = some (AXPushParam.relocate 1307 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1332_p18 : resolveAt exactSites 1350 = some (AXPushParam.relocate 1307 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1332_p : AXPushParam.Bound exactSites 1307 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1332_p0
  · exact row1332_p1
  · exact row1332_p2
  · exact row1332_p3
  · exact row1332_p4
  · exact row1332_p5
  · exact row1332_p6
  · exact row1332_p7
  · exact row1332_p8
  · exact row1332_p9
  · exact row1332_p10
  · exact row1332_p11
  · exact row1332_p12
  · exact row1332_p13
  · exact row1332_p14
  · exact row1332_p15
  · exact row1332_p16
  · exact row1332_p17
  · exact row1332_p18
theorem block1332 : AXMacro.Realizes exactSites .push 1332 1351 :=
  AXMacro.push_realizes bound1332_p
private theorem row1351_c0 : resolveAt exactSites 1351 = some (CopyToT.expected 4 1351 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1351_c1 : resolveAt exactSites 1352 = some (CopyToT.expected 4 1351 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1351_c2 : resolveAt exactSites 1353 = some (CopyToT.expected 4 1351 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1351_c3 : resolveAt exactSites 1354 = some (CopyToT.expected 4 1351 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1351_c4 : resolveAt exactSites 1355 = some (CopyToT.expected 4 1351 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1351_c5 : resolveAt exactSites 1356 = some (CopyToT.expected 4 1351 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1351_c6 : resolveAt exactSites 1357 = some (CopyToT.expected 4 1351 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1351_c : CopyToT.Bound exactSites 4 1351 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1351_c0
  · exact row1351_c1
  · exact row1351_c2
  · exact row1351_c3
  · exact row1351_c4
  · exact row1351_c5
  · exact row1351_c6
theorem block1351 : AXMacro.Realizes exactSites .copyD 1351 1358 :=
  AXMacro.copyD_realizes bound1351_c
private theorem row1358_p0 : resolveAt exactSites 1358 = some (AXPushParam.relocate 1333 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p1 : resolveAt exactSites 1359 = some (AXPushParam.relocate 1333 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p2 : resolveAt exactSites 1360 = some (AXPushParam.relocate 1333 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p3 : resolveAt exactSites 1361 = some (AXPushParam.relocate 1333 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p4 : resolveAt exactSites 1362 = some (AXPushParam.relocate 1333 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p5 : resolveAt exactSites 1363 = some (AXPushParam.relocate 1333 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p6 : resolveAt exactSites 1364 = some (AXPushParam.relocate 1333 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p7 : resolveAt exactSites 1365 = some (AXPushParam.relocate 1333 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p8 : resolveAt exactSites 1366 = some (AXPushParam.relocate 1333 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p9 : resolveAt exactSites 1367 = some (AXPushParam.relocate 1333 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p10 : resolveAt exactSites 1368 = some (AXPushParam.relocate 1333 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p11 : resolveAt exactSites 1369 = some (AXPushParam.relocate 1333 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p12 : resolveAt exactSites 1370 = some (AXPushParam.relocate 1333 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p13 : resolveAt exactSites 1371 = some (AXPushParam.relocate 1333 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p14 : resolveAt exactSites 1372 = some (AXPushParam.relocate 1333 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p15 : resolveAt exactSites 1373 = some (AXPushParam.relocate 1333 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p16 : resolveAt exactSites 1374 = some (AXPushParam.relocate 1333 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p17 : resolveAt exactSites 1375 = some (AXPushParam.relocate 1333 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1358_p18 : resolveAt exactSites 1376 = some (AXPushParam.relocate 1333 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1358_p : AXPushParam.Bound exactSites 1333 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1358_p0
  · exact row1358_p1
  · exact row1358_p2
  · exact row1358_p3
  · exact row1358_p4
  · exact row1358_p5
  · exact row1358_p6
  · exact row1358_p7
  · exact row1358_p8
  · exact row1358_p9
  · exact row1358_p10
  · exact row1358_p11
  · exact row1358_p12
  · exact row1358_p13
  · exact row1358_p14
  · exact row1358_p15
  · exact row1358_p16
  · exact row1358_p17
  · exact row1358_p18
theorem block1358 : AXMacro.Realizes exactSites .push 1358 1377 :=
  AXMacro.push_realizes bound1358_p
private theorem row1377_c0 : resolveAt exactSites 1377 = some (CopyToT.expected 5 1377 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1377_c1 : resolveAt exactSites 1378 = some (CopyToT.expected 5 1377 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1377_c2 : resolveAt exactSites 1379 = some (CopyToT.expected 5 1377 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1377_c3 : resolveAt exactSites 1380 = some (CopyToT.expected 5 1377 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1377_c4 : resolveAt exactSites 1381 = some (CopyToT.expected 5 1377 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1377_c5 : resolveAt exactSites 1382 = some (CopyToT.expected 5 1377 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1377_c6 : resolveAt exactSites 1383 = some (CopyToT.expected 5 1377 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1377_c : CopyToT.Bound exactSites 5 1377 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1377_c0
  · exact row1377_c1
  · exact row1377_c2
  · exact row1377_c3
  · exact row1377_c4
  · exact row1377_c5
  · exact row1377_c6
theorem block1377 : AXMacro.Realizes exactSites .copyH 1377 1384 :=
  AXMacro.copyH_realizes bound1377_c
private theorem row1384_u0 : resolveAt exactSites 1384 = some (UnpairPartial.expected 1384 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_u1 : resolveAt exactSites 1385 = some (UnpairPartial.expected 1384 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_u2 : resolveAt exactSites 1386 = some (UnpairPartial.expected 1384 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_u3 : resolveAt exactSites 1387 = some (UnpairPartial.expected 1384 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_u4 : resolveAt exactSites 1388 = some (UnpairPartial.expected 1384 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_u5 : resolveAt exactSites 1389 = some (UnpairPartial.expected 1384 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_u6 : resolveAt exactSites 1390 = some (UnpairPartial.expected 1384 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_u7 : resolveAt exactSites 1391 = some (UnpairPartial.expected 1384 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_u8 : resolveAt exactSites 1392 = some (UnpairPartial.expected 1384 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_u9 : resolveAt exactSites 1393 = some (UnpairPartial.expected 1384 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_u10 : resolveAt exactSites 1394 = some (UnpairPartial.expected 1384 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1384_u : UnpairPartial.Bound exactSites 1384 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1384_u0
  · exact row1384_u1
  · exact row1384_u2
  · exact row1384_u3
  · exact row1384_u4
  · exact row1384_u5
  · exact row1384_u6
  · exact row1384_u7
  · exact row1384_u8
  · exact row1384_u9
  · exact row1384_u10
private theorem row1384_q0 : resolveAt exactSites 1395 = some (AXPair.relocate 1364 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_q1 : resolveAt exactSites 1396 = some (AXPair.relocate 1364 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_q2 : resolveAt exactSites 1397 = some (AXPair.relocate 1364 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_q3 : resolveAt exactSites 1398 = some (AXPair.relocate 1364 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_q4 : resolveAt exactSites 1399 = some (AXPair.relocate 1364 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_q5 : resolveAt exactSites 1400 = some (AXPair.relocate 1364 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_q6 : resolveAt exactSites 1401 = some (AXPair.relocate 1364 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_q7 : resolveAt exactSites 1402 = some (AXPair.relocate 1364 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_q8 : resolveAt exactSites 1403 = some (AXPair.relocate 1364 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_q9 : resolveAt exactSites 1404 = some (AXPair.relocate 1364 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1384_q : AXPair.Bound exactSites 1364 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1384_q0
  · exact row1384_q1
  · exact row1384_q2
  · exact row1384_q3
  · exact row1384_q4
  · exact row1384_q5
  · exact row1384_q6
  · exact row1384_q7
  · exact row1384_q8
  · exact row1384_q9
private theorem row1384_m0 : resolveAt exactSites 1405 = some (AXTimes4.expected 1405 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_m1 : resolveAt exactSites 1406 = some (AXTimes4.expected 1405 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_m2 : resolveAt exactSites 1407 = some (AXTimes4.expected 1405 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_m3 : resolveAt exactSites 1408 = some (AXTimes4.expected 1405 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_m4 : resolveAt exactSites 1409 = some (AXTimes4.expected 1405 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1384_m5 : resolveAt exactSites 1410 = some (AXTimes4.expected 1405 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1384_m : AXTimes4.Bound exactSites 1405 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1384_m0
  · exact row1384_m1
  · exact row1384_m2
  · exact row1384_m3
  · exact row1384_m4
  · exact row1384_m5
theorem block1384 : AXMacro.Realizes exactSites .cons 1384 1411 :=
  AXMacro.cons_realizes bound1384_u bound1384_q bound1384_m
private theorem row1411_i0 : resolveAt exactSites 1411 = some (Instruction.inc 1 (some 1412)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block1411 : AXMacro.Realizes exactSites .incT 1411 1412 :=
  AXMacro.inc_realizes row1411_i0
private theorem row1412_u0 : resolveAt exactSites 1412 = some (UnpairPartial.expected 1412 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_u1 : resolveAt exactSites 1413 = some (UnpairPartial.expected 1412 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_u2 : resolveAt exactSites 1414 = some (UnpairPartial.expected 1412 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_u3 : resolveAt exactSites 1415 = some (UnpairPartial.expected 1412 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_u4 : resolveAt exactSites 1416 = some (UnpairPartial.expected 1412 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_u5 : resolveAt exactSites 1417 = some (UnpairPartial.expected 1412 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_u6 : resolveAt exactSites 1418 = some (UnpairPartial.expected 1412 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_u7 : resolveAt exactSites 1419 = some (UnpairPartial.expected 1412 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_u8 : resolveAt exactSites 1420 = some (UnpairPartial.expected 1412 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_u9 : resolveAt exactSites 1421 = some (UnpairPartial.expected 1412 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_u10 : resolveAt exactSites 1422 = some (UnpairPartial.expected 1412 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1412_u : UnpairPartial.Bound exactSites 1412 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1412_u0
  · exact row1412_u1
  · exact row1412_u2
  · exact row1412_u3
  · exact row1412_u4
  · exact row1412_u5
  · exact row1412_u6
  · exact row1412_u7
  · exact row1412_u8
  · exact row1412_u9
  · exact row1412_u10
private theorem row1412_q0 : resolveAt exactSites 1423 = some (AXPair.relocate 1392 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_q1 : resolveAt exactSites 1424 = some (AXPair.relocate 1392 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_q2 : resolveAt exactSites 1425 = some (AXPair.relocate 1392 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_q3 : resolveAt exactSites 1426 = some (AXPair.relocate 1392 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_q4 : resolveAt exactSites 1427 = some (AXPair.relocate 1392 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_q5 : resolveAt exactSites 1428 = some (AXPair.relocate 1392 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_q6 : resolveAt exactSites 1429 = some (AXPair.relocate 1392 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_q7 : resolveAt exactSites 1430 = some (AXPair.relocate 1392 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_q8 : resolveAt exactSites 1431 = some (AXPair.relocate 1392 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_q9 : resolveAt exactSites 1432 = some (AXPair.relocate 1392 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1412_q : AXPair.Bound exactSites 1392 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1412_q0
  · exact row1412_q1
  · exact row1412_q2
  · exact row1412_q3
  · exact row1412_q4
  · exact row1412_q5
  · exact row1412_q6
  · exact row1412_q7
  · exact row1412_q8
  · exact row1412_q9
private theorem row1412_m0 : resolveAt exactSites 1433 = some (AXTimes4.expected 1433 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_m1 : resolveAt exactSites 1434 = some (AXTimes4.expected 1433 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_m2 : resolveAt exactSites 1435 = some (AXTimes4.expected 1433 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_m3 : resolveAt exactSites 1436 = some (AXTimes4.expected 1433 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_m4 : resolveAt exactSites 1437 = some (AXTimes4.expected 1433 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1412_m5 : resolveAt exactSites 1438 = some (AXTimes4.expected 1433 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1412_m : AXTimes4.Bound exactSites 1433 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1412_m0
  · exact row1412_m1
  · exact row1412_m2
  · exact row1412_m3
  · exact row1412_m4
  · exact row1412_m5
theorem block1412 : AXMacro.Realizes exactSites .cons 1412 1439 :=
  AXMacro.cons_realizes bound1412_u bound1412_q bound1412_m
private theorem row1439_u0 : resolveAt exactSites 1439 = some (UnpairPartial.expected 1439 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_u1 : resolveAt exactSites 1440 = some (UnpairPartial.expected 1439 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_u2 : resolveAt exactSites 1441 = some (UnpairPartial.expected 1439 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_u3 : resolveAt exactSites 1442 = some (UnpairPartial.expected 1439 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_u4 : resolveAt exactSites 1443 = some (UnpairPartial.expected 1439 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_u5 : resolveAt exactSites 1444 = some (UnpairPartial.expected 1439 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_u6 : resolveAt exactSites 1445 = some (UnpairPartial.expected 1439 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_u7 : resolveAt exactSites 1446 = some (UnpairPartial.expected 1439 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_u8 : resolveAt exactSites 1447 = some (UnpairPartial.expected 1439 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_u9 : resolveAt exactSites 1448 = some (UnpairPartial.expected 1439 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_u10 : resolveAt exactSites 1449 = some (UnpairPartial.expected 1439 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1439_u : UnpairPartial.Bound exactSites 1439 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1439_u0
  · exact row1439_u1
  · exact row1439_u2
  · exact row1439_u3
  · exact row1439_u4
  · exact row1439_u5
  · exact row1439_u6
  · exact row1439_u7
  · exact row1439_u8
  · exact row1439_u9
  · exact row1439_u10
private theorem row1439_q0 : resolveAt exactSites 1450 = some (AXPair.relocate 1419 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_q1 : resolveAt exactSites 1451 = some (AXPair.relocate 1419 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_q2 : resolveAt exactSites 1452 = some (AXPair.relocate 1419 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_q3 : resolveAt exactSites 1453 = some (AXPair.relocate 1419 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_q4 : resolveAt exactSites 1454 = some (AXPair.relocate 1419 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_q5 : resolveAt exactSites 1455 = some (AXPair.relocate 1419 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_q6 : resolveAt exactSites 1456 = some (AXPair.relocate 1419 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_q7 : resolveAt exactSites 1457 = some (AXPair.relocate 1419 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_q8 : resolveAt exactSites 1458 = some (AXPair.relocate 1419 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_q9 : resolveAt exactSites 1459 = some (AXPair.relocate 1419 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1439_q : AXPair.Bound exactSites 1419 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1439_q0
  · exact row1439_q1
  · exact row1439_q2
  · exact row1439_q3
  · exact row1439_q4
  · exact row1439_q5
  · exact row1439_q6
  · exact row1439_q7
  · exact row1439_q8
  · exact row1439_q9
private theorem row1439_m0 : resolveAt exactSites 1460 = some (AXTimes4.expected 1460 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_m1 : resolveAt exactSites 1461 = some (AXTimes4.expected 1460 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_m2 : resolveAt exactSites 1462 = some (AXTimes4.expected 1460 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_m3 : resolveAt exactSites 1463 = some (AXTimes4.expected 1460 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_m4 : resolveAt exactSites 1464 = some (AXTimes4.expected 1460 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1439_m5 : resolveAt exactSites 1465 = some (AXTimes4.expected 1460 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1439_m : AXTimes4.Bound exactSites 1460 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1439_m0
  · exact row1439_m1
  · exact row1439_m2
  · exact row1439_m3
  · exact row1439_m4
  · exact row1439_m5
theorem block1439 : AXMacro.Realizes exactSites .cons 1439 1466 :=
  AXMacro.cons_realizes bound1439_u bound1439_q bound1439_m
private theorem row1466_p0 : resolveAt exactSites 1466 = some (AXPushParam.relocate 1441 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p1 : resolveAt exactSites 1467 = some (AXPushParam.relocate 1441 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p2 : resolveAt exactSites 1468 = some (AXPushParam.relocate 1441 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p3 : resolveAt exactSites 1469 = some (AXPushParam.relocate 1441 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p4 : resolveAt exactSites 1470 = some (AXPushParam.relocate 1441 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p5 : resolveAt exactSites 1471 = some (AXPushParam.relocate 1441 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p6 : resolveAt exactSites 1472 = some (AXPushParam.relocate 1441 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p7 : resolveAt exactSites 1473 = some (AXPushParam.relocate 1441 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p8 : resolveAt exactSites 1474 = some (AXPushParam.relocate 1441 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p9 : resolveAt exactSites 1475 = some (AXPushParam.relocate 1441 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p10 : resolveAt exactSites 1476 = some (AXPushParam.relocate 1441 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p11 : resolveAt exactSites 1477 = some (AXPushParam.relocate 1441 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p12 : resolveAt exactSites 1478 = some (AXPushParam.relocate 1441 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p13 : resolveAt exactSites 1479 = some (AXPushParam.relocate 1441 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p14 : resolveAt exactSites 1480 = some (AXPushParam.relocate 1441 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p15 : resolveAt exactSites 1481 = some (AXPushParam.relocate 1441 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p16 : resolveAt exactSites 1482 = some (AXPushParam.relocate 1441 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p17 : resolveAt exactSites 1483 = some (AXPushParam.relocate 1441 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row1466_p18 : resolveAt exactSites 1484 = some (AXPushParam.relocate 1441 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound1466_p : AXPushParam.Bound exactSites 1441 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1466_p0
  · exact row1466_p1
  · exact row1466_p2
  · exact row1466_p3
  · exact row1466_p4
  · exact row1466_p5
  · exact row1466_p6
  · exact row1466_p7
  · exact row1466_p8
  · exact row1466_p9
  · exact row1466_p10
  · exact row1466_p11
  · exact row1466_p12
  · exact row1466_p13
  · exact row1466_p14
  · exact row1466_p15
  · exact row1466_p16
  · exact row1466_p17
  · exact row1466_p18
theorem block1466 : AXMacro.Realizes exactSites .push 1466 1485 :=
  AXMacro.push_realizes bound1466_p
def code008 : List AXMacro.Op := [.copyH,.cons,.incT,.push,.copyD,.push,.copyH,.cons,.incT,.cons,.cons,.push]
theorem plan008 : AXMacro.Plan exactSites 1297 1485 code008 :=
  AXMacro.Plan.cons block1297 ( AXMacro.Plan.cons block1304 ( AXMacro.Plan.cons block1331 ( AXMacro.Plan.cons block1332 ( AXMacro.Plan.cons block1351 ( AXMacro.Plan.cons block1358 ( AXMacro.Plan.cons block1377 ( AXMacro.Plan.cons block1384 ( AXMacro.Plan.cons block1411 ( AXMacro.Plan.cons block1412 ( AXMacro.Plan.cons block1439 ( AXMacro.Plan.cons block1466 ( AXMacro.Plan.nil 1485))))))))))))
#print axioms plan008
end M6.Source.AXAll

