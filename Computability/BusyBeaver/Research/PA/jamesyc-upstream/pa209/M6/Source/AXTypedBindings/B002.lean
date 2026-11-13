module
public import M6.Source.AXBindings.B002
import all M6.Source.AXBindings.B002
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem bound371_p : AXPushParam.Bound exactSites 346 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound371_p"
theorem bound390_c : CopyToT.Bound exactSites 3 390 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound390_c"
theorem bound397_u : UnpairPartial.Bound exactSites 397 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound397_u"
theorem bound397_q : AXPair.Bound exactSites 377 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound397_q"
theorem bound397_m : AXTimes4.Bound exactSites 418 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound397_m"
theorem bound424_u : UnpairPartial.Bound exactSites 424 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound424_u"
theorem bound424_q : AXPair.Bound exactSites 404 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound424_q"
theorem bound424_m : AXTimes4.Bound exactSites 445 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound424_m"
theorem bound451_u : UnpairPartial.Bound exactSites 451 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound451_u"
theorem bound451_q : AXPair.Bound exactSites 431 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound451_q"
theorem bound451_m : AXTimes4.Bound exactSites 472 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound451_m"
theorem bound478_p : AXPushParam.Bound exactSites 453 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound478_p"
theorem bound497_c : CopyToT.Bound exactSites 3 497 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound497_c"
theorem bound504_p : AXPushParam.Bound exactSites 479 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound504_p"
theorem bound523_c : CopyToT.Bound exactSites 4 523 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound523_c"
theorem bound530_u : UnpairPartial.Bound exactSites 530 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound530_u"
theorem bound530_q : AXPair.Bound exactSites 510 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound530_q"
theorem bound530_m : AXTimes4.Bound exactSites 551 :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.bound530_m"
theorem row557_i0 : resolveAt exactSites 557 = some (Instruction.inc 1 (some 558)) :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.row557_i0"
theorem row558_i0 : resolveAt exactSites 558 = some (Instruction.inc 1 (some 559)) :=
  existingPrivateBound% "M6.Source.AXBindings.B002" "M6.Source.AXAll.row558_i0"
theorem block371 : AXTyped.Bound .push 371 390 :=
  AXTyped.Bound.push 346 (by decide) bound371_p
theorem block390 : AXTyped.Bound .copyA 390 397 :=
  AXTyped.Bound.copyA 390 (by decide) bound390_c
theorem block397 : AXTyped.Bound .cons 397 424 :=
  AXTyped.Bound.cons 377 (by decide) bound397_u bound397_q bound397_m
theorem block424 : AXTyped.Bound .cons 424 451 :=
  AXTyped.Bound.cons 404 (by decide) bound424_u bound424_q bound424_m
theorem block451 : AXTyped.Bound .cons 451 478 :=
  AXTyped.Bound.cons 431 (by decide) bound451_u bound451_q bound451_m
theorem block478 : AXTyped.Bound .push 478 497 :=
  AXTyped.Bound.push 453 (by decide) bound478_p
theorem block497 : AXTyped.Bound .copyA 497 504 :=
  AXTyped.Bound.copyA 497 (by decide) bound497_c
theorem block504 : AXTyped.Bound .push 504 523 :=
  AXTyped.Bound.push 479 (by decide) bound504_p
theorem block523 : AXTyped.Bound .copyD 523 530 :=
  AXTyped.Bound.copyD 523 (by decide) bound523_c
theorem block530 : AXTyped.Bound .cons 530 557 :=
  AXTyped.Bound.cons 510 (by decide) bound530_u bound530_q bound530_m
theorem block557 : AXTyped.Bound .incT 557 558 :=
  AXTyped.Bound.incT 557 (by decide) row557_i0
theorem block558 : AXTyped.Bound .incT 558 559 :=
  AXTyped.Bound.incT 558 (by decide) row558_i0
end M6.Source.AXModelBounds

