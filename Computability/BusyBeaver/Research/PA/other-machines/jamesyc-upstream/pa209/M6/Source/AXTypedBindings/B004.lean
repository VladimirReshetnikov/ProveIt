module
public import M6.Source.AXBindings.B004
import all M6.Source.AXBindings.B004
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem bound687_c : CopyToT.Bound exactSites 5 687 :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.bound687_c"
theorem bound694_u : UnpairPartial.Bound exactSites 694 :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.bound694_u"
theorem bound694_q : AXPair.Bound exactSites 674 :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.bound694_q"
theorem bound694_m : AXTimes4.Bound exactSites 715 :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.bound694_m"
theorem row721_i0 : resolveAt exactSites 721 = some (Instruction.inc 1 (some 722)) :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.row721_i0"
theorem bound722_p : AXPushParam.Bound exactSites 697 :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.bound722_p"
theorem bound741_c : CopyToT.Bound exactSites 4 741 :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.bound741_c"
theorem bound748_p : AXPushParam.Bound exactSites 723 :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.bound748_p"
theorem bound767_c : CopyToT.Bound exactSites 5 767 :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.bound767_c"
theorem bound774_u : UnpairPartial.Bound exactSites 774 :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.bound774_u"
theorem bound774_q : AXPair.Bound exactSites 754 :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.bound774_q"
theorem bound774_m : AXTimes4.Bound exactSites 795 :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.bound774_m"
theorem row801_i0 : resolveAt exactSites 801 = some (Instruction.inc 1 (some 802)) :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.row801_i0"
theorem row802_i0 : resolveAt exactSites 802 = some (Instruction.inc 1 (some 803)) :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.row802_i0"
theorem row803_i0 : resolveAt exactSites 803 = some (Instruction.inc 1 (some 804)) :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.row803_i0"
theorem bound804_u : UnpairPartial.Bound exactSites 804 :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.bound804_u"
theorem bound804_q : AXPair.Bound exactSites 784 :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.bound804_q"
theorem bound804_m : AXTimes4.Bound exactSites 825 :=
  existingPrivateBound% "M6.Source.AXBindings.B004" "M6.Source.AXAll.bound804_m"
theorem block687 : AXTyped.Bound .copyH 687 694 :=
  AXTyped.Bound.copyH 687 (by decide) bound687_c
theorem block694 : AXTyped.Bound .cons 694 721 :=
  AXTyped.Bound.cons 674 (by decide) bound694_u bound694_q bound694_m
theorem block721 : AXTyped.Bound .incT 721 722 :=
  AXTyped.Bound.incT 721 (by decide) row721_i0
theorem block722 : AXTyped.Bound .push 722 741 :=
  AXTyped.Bound.push 697 (by decide) bound722_p
theorem block741 : AXTyped.Bound .copyD 741 748 :=
  AXTyped.Bound.copyD 741 (by decide) bound741_c
theorem block748 : AXTyped.Bound .push 748 767 :=
  AXTyped.Bound.push 723 (by decide) bound748_p
theorem block767 : AXTyped.Bound .copyH 767 774 :=
  AXTyped.Bound.copyH 767 (by decide) bound767_c
theorem block774 : AXTyped.Bound .cons 774 801 :=
  AXTyped.Bound.cons 754 (by decide) bound774_u bound774_q bound774_m
theorem block801 : AXTyped.Bound .incT 801 802 :=
  AXTyped.Bound.incT 801 (by decide) row801_i0
theorem block802 : AXTyped.Bound .incT 802 803 :=
  AXTyped.Bound.incT 802 (by decide) row802_i0
theorem block803 : AXTyped.Bound .incT 803 804 :=
  AXTyped.Bound.incT 803 (by decide) row803_i0
theorem block804 : AXTyped.Bound .cons 804 831 :=
  AXTyped.Bound.cons 784 (by decide) bound804_u bound804_q bound804_m
end M6.Source.AXModelBounds

