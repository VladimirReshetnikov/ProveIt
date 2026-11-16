module
public import M6.Source.AXBindings.B008
import all M6.Source.AXBindings.B008
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem bound1297_c : CopyToT.Bound exactSites 5 1297 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1297_c"
theorem bound1304_u : UnpairPartial.Bound exactSites 1304 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1304_u"
theorem bound1304_q : AXPair.Bound exactSites 1284 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1304_q"
theorem bound1304_m : AXTimes4.Bound exactSites 1325 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1304_m"
theorem row1331_i0 : resolveAt exactSites 1331 = some (Instruction.inc 1 (some 1332)) :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.row1331_i0"
theorem bound1332_p : AXPushParam.Bound exactSites 1307 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1332_p"
theorem bound1351_c : CopyToT.Bound exactSites 4 1351 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1351_c"
theorem bound1358_p : AXPushParam.Bound exactSites 1333 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1358_p"
theorem bound1377_c : CopyToT.Bound exactSites 5 1377 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1377_c"
theorem bound1384_u : UnpairPartial.Bound exactSites 1384 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1384_u"
theorem bound1384_q : AXPair.Bound exactSites 1364 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1384_q"
theorem bound1384_m : AXTimes4.Bound exactSites 1405 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1384_m"
theorem row1411_i0 : resolveAt exactSites 1411 = some (Instruction.inc 1 (some 1412)) :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.row1411_i0"
theorem bound1412_u : UnpairPartial.Bound exactSites 1412 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1412_u"
theorem bound1412_q : AXPair.Bound exactSites 1392 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1412_q"
theorem bound1412_m : AXTimes4.Bound exactSites 1433 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1412_m"
theorem bound1439_u : UnpairPartial.Bound exactSites 1439 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1439_u"
theorem bound1439_q : AXPair.Bound exactSites 1419 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1439_q"
theorem bound1439_m : AXTimes4.Bound exactSites 1460 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1439_m"
theorem bound1466_p : AXPushParam.Bound exactSites 1441 :=
  existingPrivateBound% "M6.Source.AXBindings.B008" "M6.Source.AXAll.bound1466_p"
theorem block1297 : AXTyped.Bound .copyH 1297 1304 :=
  AXTyped.Bound.copyH 1297 (by decide) bound1297_c
theorem block1304 : AXTyped.Bound .cons 1304 1331 :=
  AXTyped.Bound.cons 1284 (by decide) bound1304_u bound1304_q bound1304_m
theorem block1331 : AXTyped.Bound .incT 1331 1332 :=
  AXTyped.Bound.incT 1331 (by decide) row1331_i0
theorem block1332 : AXTyped.Bound .push 1332 1351 :=
  AXTyped.Bound.push 1307 (by decide) bound1332_p
theorem block1351 : AXTyped.Bound .copyD 1351 1358 :=
  AXTyped.Bound.copyD 1351 (by decide) bound1351_c
theorem block1358 : AXTyped.Bound .push 1358 1377 :=
  AXTyped.Bound.push 1333 (by decide) bound1358_p
theorem block1377 : AXTyped.Bound .copyH 1377 1384 :=
  AXTyped.Bound.copyH 1377 (by decide) bound1377_c
theorem block1384 : AXTyped.Bound .cons 1384 1411 :=
  AXTyped.Bound.cons 1364 (by decide) bound1384_u bound1384_q bound1384_m
theorem block1411 : AXTyped.Bound .incT 1411 1412 :=
  AXTyped.Bound.incT 1411 (by decide) row1411_i0
theorem block1412 : AXTyped.Bound .cons 1412 1439 :=
  AXTyped.Bound.cons 1392 (by decide) bound1412_u bound1412_q bound1412_m
theorem block1439 : AXTyped.Bound .cons 1439 1466 :=
  AXTyped.Bound.cons 1419 (by decide) bound1439_u bound1439_q bound1439_m
theorem block1466 : AXTyped.Bound .push 1466 1485 :=
  AXTyped.Bound.push 1441 (by decide) bound1466_p
end M6.Source.AXModelBounds

