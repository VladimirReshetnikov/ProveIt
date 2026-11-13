module
public import M6.Source.AXBindings.B007
import all M6.Source.AXBindings.B007
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem bound1143_u : UnpairPartial.Bound exactSites 1143 :=
  existingPrivateBound% "M6.Source.AXBindings.B007" "M6.Source.AXAll.bound1143_u"
theorem bound1143_q : AXPair.Bound exactSites 1123 :=
  existingPrivateBound% "M6.Source.AXBindings.B007" "M6.Source.AXAll.bound1143_q"
theorem bound1143_m : AXTimes4.Bound exactSites 1164 :=
  existingPrivateBound% "M6.Source.AXBindings.B007" "M6.Source.AXAll.bound1143_m"
theorem bound1170_p : AXPushParam.Bound exactSites 1145 :=
  existingPrivateBound% "M6.Source.AXBindings.B007" "M6.Source.AXAll.bound1170_p"
theorem bound1189_c : CopyToT.Bound exactSites 3 1189 :=
  existingPrivateBound% "M6.Source.AXBindings.B007" "M6.Source.AXAll.bound1189_c"
theorem bound1196_p : AXPushParam.Bound exactSites 1171 :=
  existingPrivateBound% "M6.Source.AXBindings.B007" "M6.Source.AXAll.bound1196_p"
theorem bound1215_c : CopyToT.Bound exactSites 4 1215 :=
  existingPrivateBound% "M6.Source.AXBindings.B007" "M6.Source.AXAll.bound1215_c"
theorem bound1222_u : UnpairPartial.Bound exactSites 1222 :=
  existingPrivateBound% "M6.Source.AXBindings.B007" "M6.Source.AXAll.bound1222_u"
theorem bound1222_q : AXPair.Bound exactSites 1202 :=
  existingPrivateBound% "M6.Source.AXBindings.B007" "M6.Source.AXAll.bound1222_q"
theorem bound1222_m : AXTimes4.Bound exactSites 1243 :=
  existingPrivateBound% "M6.Source.AXBindings.B007" "M6.Source.AXAll.bound1222_m"
theorem row1249_i0 : resolveAt exactSites 1249 = some (Instruction.inc 1 (some 1250)) :=
  existingPrivateBound% "M6.Source.AXBindings.B007" "M6.Source.AXAll.row1249_i0"
theorem row1250_i0 : resolveAt exactSites 1250 = some (Instruction.inc 1 (some 1251)) :=
  existingPrivateBound% "M6.Source.AXBindings.B007" "M6.Source.AXAll.row1250_i0"
theorem row1251_i0 : resolveAt exactSites 1251 = some (Instruction.inc 1 (some 1252)) :=
  existingPrivateBound% "M6.Source.AXBindings.B007" "M6.Source.AXAll.row1251_i0"
theorem bound1252_p : AXPushParam.Bound exactSites 1227 :=
  existingPrivateBound% "M6.Source.AXBindings.B007" "M6.Source.AXAll.bound1252_p"
theorem bound1271_c : CopyToT.Bound exactSites 3 1271 :=
  existingPrivateBound% "M6.Source.AXBindings.B007" "M6.Source.AXAll.bound1271_c"
theorem bound1278_p : AXPushParam.Bound exactSites 1253 :=
  existingPrivateBound% "M6.Source.AXBindings.B007" "M6.Source.AXAll.bound1278_p"
theorem block1143 : AXTyped.Bound .cons 1143 1170 :=
  AXTyped.Bound.cons 1123 (by decide) bound1143_u bound1143_q bound1143_m
theorem block1170 : AXTyped.Bound .push 1170 1189 :=
  AXTyped.Bound.push 1145 (by decide) bound1170_p
theorem block1189 : AXTyped.Bound .copyA 1189 1196 :=
  AXTyped.Bound.copyA 1189 (by decide) bound1189_c
theorem block1196 : AXTyped.Bound .push 1196 1215 :=
  AXTyped.Bound.push 1171 (by decide) bound1196_p
theorem block1215 : AXTyped.Bound .copyD 1215 1222 :=
  AXTyped.Bound.copyD 1215 (by decide) bound1215_c
theorem block1222 : AXTyped.Bound .cons 1222 1249 :=
  AXTyped.Bound.cons 1202 (by decide) bound1222_u bound1222_q bound1222_m
theorem block1249 : AXTyped.Bound .incT 1249 1250 :=
  AXTyped.Bound.incT 1249 (by decide) row1249_i0
theorem block1250 : AXTyped.Bound .incT 1250 1251 :=
  AXTyped.Bound.incT 1250 (by decide) row1250_i0
theorem block1251 : AXTyped.Bound .incT 1251 1252 :=
  AXTyped.Bound.incT 1251 (by decide) row1251_i0
theorem block1252 : AXTyped.Bound .push 1252 1271 :=
  AXTyped.Bound.push 1227 (by decide) bound1252_p
theorem block1271 : AXTyped.Bound .copyA 1271 1278 :=
  AXTyped.Bound.copyA 1271 (by decide) bound1271_c
theorem block1278 : AXTyped.Bound .push 1278 1297 :=
  AXTyped.Bound.push 1253 (by decide) bound1278_p
end M6.Source.AXModelBounds

