module
public import M6.Source.AXBindings.B003
import all M6.Source.AXBindings.B003
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem row559_i0 : resolveAt exactSites 559 = some (Instruction.inc 1 (some 560)) :=
  existingPrivateBound% "M6.Source.AXBindings.B003" "M6.Source.AXAll.row559_i0"
theorem bound560_p : AXPushParam.Bound exactSites 535 :=
  existingPrivateBound% "M6.Source.AXBindings.B003" "M6.Source.AXAll.bound560_p"
theorem bound579_c : CopyToT.Bound exactSites 3 579 :=
  existingPrivateBound% "M6.Source.AXBindings.B003" "M6.Source.AXAll.bound579_c"
theorem bound586_p : AXPushParam.Bound exactSites 561 :=
  existingPrivateBound% "M6.Source.AXBindings.B003" "M6.Source.AXAll.bound586_p"
theorem bound605_c : CopyToT.Bound exactSites 5 605 :=
  existingPrivateBound% "M6.Source.AXBindings.B003" "M6.Source.AXAll.bound605_c"
theorem bound612_u : UnpairPartial.Bound exactSites 612 :=
  existingPrivateBound% "M6.Source.AXBindings.B003" "M6.Source.AXAll.bound612_u"
theorem bound612_q : AXPair.Bound exactSites 592 :=
  existingPrivateBound% "M6.Source.AXBindings.B003" "M6.Source.AXAll.bound612_q"
theorem bound612_m : AXTimes4.Bound exactSites 633 :=
  existingPrivateBound% "M6.Source.AXBindings.B003" "M6.Source.AXAll.bound612_m"
theorem row639_i0 : resolveAt exactSites 639 = some (Instruction.inc 1 (some 640)) :=
  existingPrivateBound% "M6.Source.AXBindings.B003" "M6.Source.AXAll.row639_i0"
theorem row640_i0 : resolveAt exactSites 640 = some (Instruction.inc 1 (some 641)) :=
  existingPrivateBound% "M6.Source.AXBindings.B003" "M6.Source.AXAll.row640_i0"
theorem row641_i0 : resolveAt exactSites 641 = some (Instruction.inc 1 (some 642)) :=
  existingPrivateBound% "M6.Source.AXBindings.B003" "M6.Source.AXAll.row641_i0"
theorem bound642_p : AXPushParam.Bound exactSites 617 :=
  existingPrivateBound% "M6.Source.AXBindings.B003" "M6.Source.AXAll.bound642_p"
theorem bound661_c : CopyToT.Bound exactSites 4 661 :=
  existingPrivateBound% "M6.Source.AXBindings.B003" "M6.Source.AXAll.bound661_c"
theorem bound668_p : AXPushParam.Bound exactSites 643 :=
  existingPrivateBound% "M6.Source.AXBindings.B003" "M6.Source.AXAll.bound668_p"
theorem block559 : AXTyped.Bound .incT 559 560 :=
  AXTyped.Bound.incT 559 (by decide) row559_i0
theorem block560 : AXTyped.Bound .push 560 579 :=
  AXTyped.Bound.push 535 (by decide) bound560_p
theorem block579 : AXTyped.Bound .copyA 579 586 :=
  AXTyped.Bound.copyA 579 (by decide) bound579_c
theorem block586 : AXTyped.Bound .push 586 605 :=
  AXTyped.Bound.push 561 (by decide) bound586_p
theorem block605 : AXTyped.Bound .copyH 605 612 :=
  AXTyped.Bound.copyH 605 (by decide) bound605_c
theorem block612 : AXTyped.Bound .cons 612 639 :=
  AXTyped.Bound.cons 592 (by decide) bound612_u bound612_q bound612_m
theorem block639 : AXTyped.Bound .incT 639 640 :=
  AXTyped.Bound.incT 639 (by decide) row639_i0
theorem block640 : AXTyped.Bound .incT 640 641 :=
  AXTyped.Bound.incT 640 (by decide) row640_i0
theorem block641 : AXTyped.Bound .incT 641 642 :=
  AXTyped.Bound.incT 641 (by decide) row641_i0
theorem block642 : AXTyped.Bound .push 642 661 :=
  AXTyped.Bound.push 617 (by decide) bound642_p
theorem block661 : AXTyped.Bound .copyD 661 668 :=
  AXTyped.Bound.copyD 661 (by decide) bound661_c
theorem block668 : AXTyped.Bound .push 668 687 :=
  AXTyped.Bound.push 643 (by decide) bound668_p
end M6.Source.AXModelBounds

