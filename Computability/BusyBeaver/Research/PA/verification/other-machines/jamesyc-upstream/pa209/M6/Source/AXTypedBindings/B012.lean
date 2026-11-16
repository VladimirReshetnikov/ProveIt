module
public import M6.Source.AXBindings.B012
import all M6.Source.AXBindings.B012
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem bound2061_p : AXPushParam.Bound exactSites 2036 :=
  existingPrivateBound% "M6.Source.AXBindings.B012" "M6.Source.AXAll.bound2061_p"
theorem bound2080_c : CopyToT.Bound exactSites 4 2080 :=
  existingPrivateBound% "M6.Source.AXBindings.B012" "M6.Source.AXAll.bound2080_c"
theorem block2061 : AXTyped.Bound .push 2061 2080 :=
  AXTyped.Bound.push 2036 (by decide) bound2061_p
theorem block2080 : AXTyped.Bound .copyD 2080 2087 :=
  AXTyped.Bound.copyD 2080 (by decide) bound2080_c
end M6.Source.AXModelBounds

