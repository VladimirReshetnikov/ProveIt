module
public import M6.Source.AXBindings.B020
import all M6.Source.AXBindings.B020
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem bound3221_c : CopyToT.Bound exactSites 5 3221 :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.bound3221_c"
theorem bound3228_u : UnpairPartial.Bound exactSites 3228 :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.bound3228_u"
theorem bound3228_q : AXPair.Bound exactSites 3208 :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.bound3228_q"
theorem bound3228_m : AXTimes4.Bound exactSites 3249 :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.bound3228_m"
theorem row3255_i0 : resolveAt exactSites 3255 = some (Instruction.inc 1 (some 3256)) :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.row3255_i0"
theorem bound3256_p : AXPushParam.Bound exactSites 3231 :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.bound3256_p"
theorem bound3275_c : CopyToT.Bound exactSites 3 3275 :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.bound3275_c"
theorem bound3282_u : UnpairPartial.Bound exactSites 3282 :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.bound3282_u"
theorem bound3282_q : AXPair.Bound exactSites 3262 :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.bound3282_q"
theorem bound3282_m : AXTimes4.Bound exactSites 3303 :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.bound3282_m"
theorem bound3309_p : AXPushParam.Bound exactSites 3284 :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.bound3309_p"
theorem row3328_i0 : resolveAt exactSites 3328 = some (Instruction.inc 1 (some 3329)) :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.row3328_i0"
theorem bound3329_u : UnpairPartial.Bound exactSites 3329 :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.bound3329_u"
theorem bound3329_q : AXPair.Bound exactSites 3309 :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.bound3329_q"
theorem bound3329_m : AXTimes4.Bound exactSites 3350 :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.bound3329_m"
theorem bound3356_u : UnpairPartial.Bound exactSites 3356 :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.bound3356_u"
theorem bound3356_q : AXPair.Bound exactSites 3336 :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.bound3356_q"
theorem bound3356_m : AXTimes4.Bound exactSites 3377 :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.bound3356_m"
theorem bound3383_p : AXPushParam.Bound exactSites 3358 :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.bound3383_p"
theorem row3402_i0 : resolveAt exactSites 3402 = some (Instruction.inc 1 (some 3403)) :=
  existingPrivateBound% "M6.Source.AXBindings.B020" "M6.Source.AXAll.row3402_i0"
theorem block3221 : AXTyped.Bound .copyH 3221 3228 :=
  AXTyped.Bound.copyH 3221 (by decide) bound3221_c
theorem block3228 : AXTyped.Bound .cons 3228 3255 :=
  AXTyped.Bound.cons 3208 (by decide) bound3228_u bound3228_q bound3228_m
theorem block3255 : AXTyped.Bound .incT 3255 3256 :=
  AXTyped.Bound.incT 3255 (by decide) row3255_i0
theorem block3256 : AXTyped.Bound .push 3256 3275 :=
  AXTyped.Bound.push 3231 (by decide) bound3256_p
theorem block3275 : AXTyped.Bound .copyA 3275 3282 :=
  AXTyped.Bound.copyA 3275 (by decide) bound3275_c
theorem block3282 : AXTyped.Bound .cons 3282 3309 :=
  AXTyped.Bound.cons 3262 (by decide) bound3282_u bound3282_q bound3282_m
theorem block3309 : AXTyped.Bound .push 3309 3328 :=
  AXTyped.Bound.push 3284 (by decide) bound3309_p
theorem block3328 : AXTyped.Bound .incT 3328 3329 :=
  AXTyped.Bound.incT 3328 (by decide) row3328_i0
theorem block3329 : AXTyped.Bound .cons 3329 3356 :=
  AXTyped.Bound.cons 3309 (by decide) bound3329_u bound3329_q bound3329_m
theorem block3356 : AXTyped.Bound .cons 3356 3383 :=
  AXTyped.Bound.cons 3336 (by decide) bound3356_u bound3356_q bound3356_m
theorem block3383 : AXTyped.Bound .push 3383 3402 :=
  AXTyped.Bound.push 3358 (by decide) bound3383_p
theorem block3402 : AXTyped.Bound .incT 3402 3403 :=
  AXTyped.Bound.incT 3402 (by decide) row3402_i0
end M6.Source.AXModelBounds

