module
public import M6.Source.AXBindings.B021
import all M6.Source.AXBindings.B021
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem bound3403_u : UnpairPartial.Bound exactSites 3403 :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.bound3403_u"
theorem bound3403_q : AXPair.Bound exactSites 3383 :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.bound3403_q"
theorem bound3403_m : AXTimes4.Bound exactSites 3424 :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.bound3403_m"
theorem bound3430_u : UnpairPartial.Bound exactSites 3430 :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.bound3430_u"
theorem bound3430_q : AXPair.Bound exactSites 3410 :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.bound3430_q"
theorem bound3430_m : AXTimes4.Bound exactSites 3451 :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.bound3430_m"
theorem row3457_i0 : resolveAt exactSites 3457 = some (Instruction.inc 1 (some 3458)) :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.row3457_i0"
theorem row3458_i0 : resolveAt exactSites 3458 = some (Instruction.inc 1 (some 3459)) :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.row3458_i0"
theorem bound3459_p : AXPushParam.Bound exactSites 3434 :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.bound3459_p"
theorem bound3478_c : CopyToT.Bound exactSites 3 3478 :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.bound3478_c"
theorem bound3485_p : AXPushParam.Bound exactSites 3460 :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.bound3485_p"
theorem bound3504_c : CopyToT.Bound exactSites 3 3504 :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.bound3504_c"
theorem bound3511_p : AXPushParam.Bound exactSites 3486 :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.bound3511_p"
theorem bound3530_c : CopyToT.Bound exactSites 5 3530 :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.bound3530_c"
theorem bound3537_u : UnpairPartial.Bound exactSites 3537 :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.bound3537_u"
theorem bound3537_q : AXPair.Bound exactSites 3517 :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.bound3537_q"
theorem bound3537_m : AXTimes4.Bound exactSites 3558 :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.bound3537_m"
theorem row3564_i0 : resolveAt exactSites 3564 = some (Instruction.inc 1 (some 3565)) :=
  existingPrivateBound% "M6.Source.AXBindings.B021" "M6.Source.AXAll.row3564_i0"
theorem block3403 : AXTyped.Bound .cons 3403 3430 :=
  AXTyped.Bound.cons 3383 (by decide) bound3403_u bound3403_q bound3403_m
theorem block3430 : AXTyped.Bound .cons 3430 3457 :=
  AXTyped.Bound.cons 3410 (by decide) bound3430_u bound3430_q bound3430_m
theorem block3457 : AXTyped.Bound .incT 3457 3458 :=
  AXTyped.Bound.incT 3457 (by decide) row3457_i0
theorem block3458 : AXTyped.Bound .incT 3458 3459 :=
  AXTyped.Bound.incT 3458 (by decide) row3458_i0
theorem block3459 : AXTyped.Bound .push 3459 3478 :=
  AXTyped.Bound.push 3434 (by decide) bound3459_p
theorem block3478 : AXTyped.Bound .copyA 3478 3485 :=
  AXTyped.Bound.copyA 3478 (by decide) bound3478_c
theorem block3485 : AXTyped.Bound .push 3485 3504 :=
  AXTyped.Bound.push 3460 (by decide) bound3485_p
theorem block3504 : AXTyped.Bound .copyA 3504 3511 :=
  AXTyped.Bound.copyA 3504 (by decide) bound3504_c
theorem block3511 : AXTyped.Bound .push 3511 3530 :=
  AXTyped.Bound.push 3486 (by decide) bound3511_p
theorem block3530 : AXTyped.Bound .copyH 3530 3537 :=
  AXTyped.Bound.copyH 3530 (by decide) bound3530_c
theorem block3537 : AXTyped.Bound .cons 3537 3564 :=
  AXTyped.Bound.cons 3517 (by decide) bound3537_u bound3537_q bound3537_m
theorem block3564 : AXTyped.Bound .incT 3564 3565 :=
  AXTyped.Bound.incT 3564 (by decide) row3564_i0
end M6.Source.AXModelBounds

