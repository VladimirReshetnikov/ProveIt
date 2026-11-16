module
public import M6.Source.AXBindings.B000
import all M6.Source.AXBindings.B000
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem bound25_p : AXPushParam.Bound exactSites 0 :=
  existingPrivateBound% "M6.Source.AXBindings.B000" "M6.Source.AXAll.bound25_p"
theorem bound44_c : CopyToT.Bound exactSites 4 44 :=
  existingPrivateBound% "M6.Source.AXBindings.B000" "M6.Source.AXAll.bound44_c"
theorem bound51_p : AXPushParam.Bound exactSites 26 :=
  existingPrivateBound% "M6.Source.AXBindings.B000" "M6.Source.AXAll.bound51_p"
theorem bound70_c : CopyToT.Bound exactSites 5 70 :=
  existingPrivateBound% "M6.Source.AXBindings.B000" "M6.Source.AXAll.bound70_c"
theorem bound77_u : UnpairPartial.Bound exactSites 77 :=
  existingPrivateBound% "M6.Source.AXBindings.B000" "M6.Source.AXAll.bound77_u"
theorem bound77_q : AXPair.Bound exactSites 57 :=
  existingPrivateBound% "M6.Source.AXBindings.B000" "M6.Source.AXAll.bound77_q"
theorem bound77_m : AXTimes4.Bound exactSites 98 :=
  existingPrivateBound% "M6.Source.AXBindings.B000" "M6.Source.AXAll.bound77_m"
theorem row104_i0 : resolveAt exactSites 104 = some (Instruction.inc 1 (some 105)) :=
  existingPrivateBound% "M6.Source.AXBindings.B000" "M6.Source.AXAll.row104_i0"
theorem row105_i0 : resolveAt exactSites 105 = some (Instruction.inc 1 (some 106)) :=
  existingPrivateBound% "M6.Source.AXBindings.B000" "M6.Source.AXAll.row105_i0"
theorem bound106_p : AXPushParam.Bound exactSites 81 :=
  existingPrivateBound% "M6.Source.AXBindings.B000" "M6.Source.AXAll.bound106_p"
theorem bound125_c : CopyToT.Bound exactSites 3 125 :=
  existingPrivateBound% "M6.Source.AXBindings.B000" "M6.Source.AXAll.bound125_c"
theorem bound132_p : AXPushParam.Bound exactSites 107 :=
  existingPrivateBound% "M6.Source.AXBindings.B000" "M6.Source.AXAll.bound132_p"
theorem bound151_c : CopyToT.Bound exactSites 4 151 :=
  existingPrivateBound% "M6.Source.AXBindings.B000" "M6.Source.AXAll.bound151_c"
theorem bound158_r : (AXMacro.readerH 158).Bound :=
  existingPrivateBound% "M6.Source.AXBindings.B000" "M6.Source.AXAll.bound158_r"
theorem block25 : AXTyped.Bound .push 25 44 :=
  AXTyped.Bound.push 0 (by decide) bound25_p
theorem block44 : AXTyped.Bound .copyD 44 51 :=
  AXTyped.Bound.copyD 44 (by decide) bound44_c
theorem block51 : AXTyped.Bound .push 51 70 :=
  AXTyped.Bound.push 26 (by decide) bound51_p
theorem block70 : AXTyped.Bound .copyH 70 77 :=
  AXTyped.Bound.copyH 70 (by decide) bound70_c
theorem block77 : AXTyped.Bound .cons 77 104 :=
  AXTyped.Bound.cons 57 (by decide) bound77_u bound77_q bound77_m
theorem block104 : AXTyped.Bound .incT 104 105 :=
  AXTyped.Bound.incT 104 (by decide) row104_i0
theorem block105 : AXTyped.Bound .incT 105 106 :=
  AXTyped.Bound.incT 105 (by decide) row105_i0
theorem block106 : AXTyped.Bound .push 106 125 :=
  AXTyped.Bound.push 81 (by decide) bound106_p
theorem block125 : AXTyped.Bound .copyA 125 132 :=
  AXTyped.Bound.copyA 125 (by decide) bound125_c
theorem block132 : AXTyped.Bound .push 132 151 :=
  AXTyped.Bound.push 107 (by decide) bound132_p
theorem block151 : AXTyped.Bound .copyD 151 158 :=
  AXTyped.Bound.copyD 151 (by decide) bound151_c
theorem block158 : AXTyped.Bound .readH 158 172 :=
  AXTyped.Bound.readH 158 (by decide) bound158_r
end M6.Source.AXModelBounds

