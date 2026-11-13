module
public import M6.Source.AXBindings.B001
import all M6.Source.AXBindings.B001
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem bound172_u : UnpairPartial.Bound exactSites 172 :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound172_u"
theorem bound172_q : AXPair.Bound exactSites 152 :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound172_q"
theorem bound172_m : AXTimes4.Bound exactSites 193 :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound172_m"
theorem bound199_r : (AXMacro.readerD 199).Bound :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound199_r"
theorem bound213_p : AXPushParam.Bound exactSites 188 :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound213_p"
theorem bound232_c : CopyToT.Bound exactSites 4 232 :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound232_c"
theorem bound239_u : UnpairPartial.Bound exactSites 239 :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound239_u"
theorem bound239_q : AXPair.Bound exactSites 219 :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound239_q"
theorem bound239_m : AXTimes4.Bound exactSites 260 :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound239_m"
theorem bound266_p : AXPushParam.Bound exactSites 241 :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound266_p"
theorem bound285_c : CopyToT.Bound exactSites 4 285 :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound285_c"
theorem bound292_p : AXPushParam.Bound exactSites 267 :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound292_p"
theorem bound311_c : CopyToT.Bound exactSites 3 311 :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound311_c"
theorem bound318_u : UnpairPartial.Bound exactSites 318 :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound318_u"
theorem bound318_q : AXPair.Bound exactSites 298 :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound318_q"
theorem bound318_m : AXTimes4.Bound exactSites 339 :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound318_m"
theorem bound345_p : AXPushParam.Bound exactSites 320 :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound345_p"
theorem bound364_c : CopyToT.Bound exactSites 5 364 :=
  existingPrivateBound% "M6.Source.AXBindings.B001" "M6.Source.AXAll.bound364_c"
theorem block172 : AXTyped.Bound .cons 172 199 :=
  AXTyped.Bound.cons 152 (by decide) bound172_u bound172_q bound172_m
theorem block199 : AXTyped.Bound .readD 199 213 :=
  AXTyped.Bound.readD 199 (by decide) bound199_r
theorem block213 : AXTyped.Bound .push 213 232 :=
  AXTyped.Bound.push 188 (by decide) bound213_p
theorem block232 : AXTyped.Bound .copyD 232 239 :=
  AXTyped.Bound.copyD 232 (by decide) bound232_c
theorem block239 : AXTyped.Bound .cons 239 266 :=
  AXTyped.Bound.cons 219 (by decide) bound239_u bound239_q bound239_m
theorem block266 : AXTyped.Bound .push 266 285 :=
  AXTyped.Bound.push 241 (by decide) bound266_p
theorem block285 : AXTyped.Bound .copyD 285 292 :=
  AXTyped.Bound.copyD 285 (by decide) bound285_c
theorem block292 : AXTyped.Bound .push 292 311 :=
  AXTyped.Bound.push 267 (by decide) bound292_p
theorem block311 : AXTyped.Bound .copyA 311 318 :=
  AXTyped.Bound.copyA 311 (by decide) bound311_c
theorem block318 : AXTyped.Bound .cons 318 345 :=
  AXTyped.Bound.cons 298 (by decide) bound318_u bound318_q bound318_m
theorem block345 : AXTyped.Bound .push 345 364 :=
  AXTyped.Bound.push 320 (by decide) bound345_p
theorem block364 : AXTyped.Bound .copyH 364 371 :=
  AXTyped.Bound.copyH 364 (by decide) bound364_c
end M6.Source.AXModelBounds

