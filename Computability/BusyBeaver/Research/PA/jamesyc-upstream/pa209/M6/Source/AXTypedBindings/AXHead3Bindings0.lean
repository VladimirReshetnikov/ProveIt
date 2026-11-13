module
public import M6.Source.AXHead3Bindings0
import all M6.Source.AXHead3Bindings0
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem bound1784_c : CopyToT.Bound exactSites 4 1784 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings0" "M6.Source.AXHead3.bound1784_c"
theorem bound1791_p : AXPushParam.Bound exactSites 1766 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings0" "M6.Source.AXHead3.bound1791_p"
theorem bound1810_c : CopyToT.Bound exactSites 5 1810 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings0" "M6.Source.AXHead3.bound1810_c"
theorem bound1817_u : UnpairPartial.Bound exactSites 1817 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings0" "M6.Source.AXHead3.bound1817_u"
theorem bound1817_q : AXPair.Bound exactSites 1797 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings0" "M6.Source.AXHead3.bound1817_q"
theorem bound1817_m : AXTimes4.Bound exactSites 1838 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings0" "M6.Source.AXHead3.bound1817_m"
theorem row1844_i0 : resolveAt exactSites 1844 = some (Instruction.inc 1 (some 1845)) :=
  existingPrivateBound% "M6.Source.AXHead3Bindings0" "M6.Source.AXHead3.row1844_i0"
theorem row1845_i0 : resolveAt exactSites 1845 = some (Instruction.inc 1 (some 1846)) :=
  existingPrivateBound% "M6.Source.AXHead3Bindings0" "M6.Source.AXHead3.row1845_i0"
theorem row1846_i0 : resolveAt exactSites 1846 = some (Instruction.inc 1 (some 1847)) :=
  existingPrivateBound% "M6.Source.AXHead3Bindings0" "M6.Source.AXHead3.row1846_i0"
theorem block1784 : AXTyped.Bound .copyD 1784 1791 :=
  AXTyped.Bound.copyD 1784 (by decide) bound1784_c
theorem block1791 : AXTyped.Bound .push 1791 1810 :=
  AXTyped.Bound.push 1766 (by decide) bound1791_p
theorem block1810 : AXTyped.Bound .copyH 1810 1817 :=
  AXTyped.Bound.copyH 1810 (by decide) bound1810_c
theorem block1817 : AXTyped.Bound .cons 1817 1844 :=
  AXTyped.Bound.cons 1797 (by decide) bound1817_u bound1817_q bound1817_m
theorem block1844 : AXTyped.Bound .incT 1844 1845 :=
  AXTyped.Bound.incT 1844 (by decide) row1844_i0
theorem block1845 : AXTyped.Bound .incT 1845 1846 :=
  AXTyped.Bound.incT 1845 (by decide) row1845_i0
theorem block1846 : AXTyped.Bound .incT 1846 1847 :=
  AXTyped.Bound.incT 1846 (by decide) row1846_i0
end M6.Source.AXModelBounds

