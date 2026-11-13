module
public import M6.Source.AXHead3Bindings1
import all M6.Source.AXHead3Bindings1
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem bound1847_p : AXPushParam.Bound exactSites 1822 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings1" "M6.Source.AXHead3.bound1847_p"
theorem bound1866_c : CopyToT.Bound exactSites 3 1866 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings1" "M6.Source.AXHead3.bound1866_c"
theorem bound1873_p : AXPushParam.Bound exactSites 1848 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings1" "M6.Source.AXHead3.bound1873_p"
theorem bound1892_c : CopyToT.Bound exactSites 4 1892 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings1" "M6.Source.AXHead3.bound1892_c"
theorem bound1899_u : UnpairPartial.Bound exactSites 1899 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings1" "M6.Source.AXHead3.bound1899_u"
theorem bound1899_q : AXPair.Bound exactSites 1879 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings1" "M6.Source.AXHead3.bound1899_q"
theorem bound1899_m : AXTimes4.Bound exactSites 1920 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings1" "M6.Source.AXHead3.bound1899_m"
theorem row1926_i0 : resolveAt exactSites 1926 = some (Instruction.inc 1 (some 1927)) :=
  existingPrivateBound% "M6.Source.AXHead3Bindings1" "M6.Source.AXHead3.row1926_i0"
theorem bound1927_p : AXPushParam.Bound exactSites 1902 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings1" "M6.Source.AXHead3.bound1927_p"
theorem block1847 : AXTyped.Bound .push 1847 1866 :=
  AXTyped.Bound.push 1822 (by decide) bound1847_p
theorem block1866 : AXTyped.Bound .copyA 1866 1873 :=
  AXTyped.Bound.copyA 1866 (by decide) bound1866_c
theorem block1873 : AXTyped.Bound .push 1873 1892 :=
  AXTyped.Bound.push 1848 (by decide) bound1873_p
theorem block1892 : AXTyped.Bound .copyD 1892 1899 :=
  AXTyped.Bound.copyD 1892 (by decide) bound1892_c
theorem block1899 : AXTyped.Bound .cons 1899 1926 :=
  AXTyped.Bound.cons 1879 (by decide) bound1899_u bound1899_q bound1899_m
theorem block1926 : AXTyped.Bound .incT 1926 1927 :=
  AXTyped.Bound.incT 1926 (by decide) row1926_i0
theorem block1927 : AXTyped.Bound .push 1927 1946 :=
  AXTyped.Bound.push 1902 (by decide) bound1927_p
end M6.Source.AXModelBounds

