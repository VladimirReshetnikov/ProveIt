module
public import M6.Source.AXBindings.B010
import all M6.Source.AXBindings.B010
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem bound1621_c : CopyToT.Bound exactSites 5 1621 :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.bound1621_c"
theorem bound1628_p : AXPushParam.Bound exactSites 1603 :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.bound1628_p"
theorem bound1647_c : CopyToT.Bound exactSites 4 1647 :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.bound1647_c"
theorem bound1654_p : AXPushParam.Bound exactSites 1629 :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.bound1654_p"
theorem bound1673_c : CopyToT.Bound exactSites 3 1673 :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.bound1673_c"
theorem bound1680_u : UnpairPartial.Bound exactSites 1680 :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.bound1680_u"
theorem bound1680_q : AXPair.Bound exactSites 1660 :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.bound1680_q"
theorem bound1680_m : AXTimes4.Bound exactSites 1701 :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.bound1680_m"
theorem row1707_i0 : resolveAt exactSites 1707 = some (Instruction.inc 1 (some 1708)) :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.row1707_i0"
theorem row1708_i0 : resolveAt exactSites 1708 = some (Instruction.inc 1 (some 1709)) :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.row1708_i0"
theorem bound1709_u : UnpairPartial.Bound exactSites 1709 :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.bound1709_u"
theorem bound1709_q : AXPair.Bound exactSites 1689 :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.bound1709_q"
theorem bound1709_m : AXTimes4.Bound exactSites 1730 :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.bound1709_m"
theorem row1736_i0 : resolveAt exactSites 1736 = some (Instruction.inc 1 (some 1737)) :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.row1736_i0"
theorem row1737_i0 : resolveAt exactSites 1737 = some (Instruction.inc 1 (some 1738)) :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.row1737_i0"
theorem bound1738_u : UnpairPartial.Bound exactSites 1738 :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.bound1738_u"
theorem bound1738_q : AXPair.Bound exactSites 1718 :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.bound1738_q"
theorem bound1738_m : AXTimes4.Bound exactSites 1759 :=
  existingPrivateBound% "M6.Source.AXBindings.B010" "M6.Source.AXAll.bound1738_m"
theorem block1621 : AXTyped.Bound .copyH 1621 1628 :=
  AXTyped.Bound.copyH 1621 (by decide) bound1621_c
theorem block1628 : AXTyped.Bound .push 1628 1647 :=
  AXTyped.Bound.push 1603 (by decide) bound1628_p
theorem block1647 : AXTyped.Bound .copyD 1647 1654 :=
  AXTyped.Bound.copyD 1647 (by decide) bound1647_c
theorem block1654 : AXTyped.Bound .push 1654 1673 :=
  AXTyped.Bound.push 1629 (by decide) bound1654_p
theorem block1673 : AXTyped.Bound .copyA 1673 1680 :=
  AXTyped.Bound.copyA 1673 (by decide) bound1673_c
theorem block1680 : AXTyped.Bound .cons 1680 1707 :=
  AXTyped.Bound.cons 1660 (by decide) bound1680_u bound1680_q bound1680_m
theorem block1707 : AXTyped.Bound .incT 1707 1708 :=
  AXTyped.Bound.incT 1707 (by decide) row1707_i0
theorem block1708 : AXTyped.Bound .incT 1708 1709 :=
  AXTyped.Bound.incT 1708 (by decide) row1708_i0
theorem block1709 : AXTyped.Bound .cons 1709 1736 :=
  AXTyped.Bound.cons 1689 (by decide) bound1709_u bound1709_q bound1709_m
theorem block1736 : AXTyped.Bound .incT 1736 1737 :=
  AXTyped.Bound.incT 1736 (by decide) row1736_i0
theorem block1737 : AXTyped.Bound .incT 1737 1738 :=
  AXTyped.Bound.incT 1737 (by decide) row1737_i0
theorem block1738 : AXTyped.Bound .cons 1738 1765 :=
  AXTyped.Bound.cons 1718 (by decide) bound1738_u bound1738_q bound1738_m
end M6.Source.AXModelBounds

