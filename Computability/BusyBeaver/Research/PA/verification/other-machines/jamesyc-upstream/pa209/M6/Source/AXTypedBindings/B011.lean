module
public import M6.Source.AXBindings.B011
import all M6.Source.AXBindings.B011
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem bound1765_p : AXPushParam.Bound exactSites 1740 :=
  existingPrivateBound% "M6.Source.AXBindings.B011" "M6.Source.AXAll.bound1765_p"
theorem block1765 : AXTyped.Bound .push 1765 1784 :=
  AXTyped.Bound.push 1740 (by decide) bound1765_p
end M6.Source.AXModelBounds

