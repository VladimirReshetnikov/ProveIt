module
public import M6.Source.AXHead3Bindings2
import all M6.Source.AXHead3Bindings2
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem bound1946_c : CopyToT.Bound exactSites 3 1946 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings2" "M6.Source.AXHead3.bound1946_c"
theorem bound1953_p : AXPushParam.Bound exactSites 1928 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings2" "M6.Source.AXHead3.bound1953_p"
theorem bound1972_c : CopyToT.Bound exactSites 5 1972 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings2" "M6.Source.AXHead3.bound1972_c"
theorem bound1979_u : UnpairPartial.Bound exactSites 1979 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings2" "M6.Source.AXHead3.bound1979_u"
theorem bound1979_q : AXPair.Bound exactSites 1959 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings2" "M6.Source.AXHead3.bound1979_q"
theorem bound1979_m : AXTimes4.Bound exactSites 2000 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings2" "M6.Source.AXHead3.bound1979_m"
theorem row2006_i0 : resolveAt exactSites 2006 = some (Instruction.inc 1 (some 2007)) :=
  existingPrivateBound% "M6.Source.AXHead3Bindings2" "M6.Source.AXHead3.row2006_i0"
theorem bound2007_u : UnpairPartial.Bound exactSites 2007 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings2" "M6.Source.AXHead3.bound2007_u"
theorem bound2007_q : AXPair.Bound exactSites 1987 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings2" "M6.Source.AXHead3.bound2007_q"
theorem bound2007_m : AXTimes4.Bound exactSites 2028 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings2" "M6.Source.AXHead3.bound2007_m"
theorem bound2034_u : UnpairPartial.Bound exactSites 2034 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings2" "M6.Source.AXHead3.bound2034_u"
theorem bound2034_q : AXPair.Bound exactSites 2014 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings2" "M6.Source.AXHead3.bound2034_q"
theorem bound2034_m : AXTimes4.Bound exactSites 2055 :=
  existingPrivateBound% "M6.Source.AXHead3Bindings2" "M6.Source.AXHead3.bound2034_m"
theorem block1946 : AXTyped.Bound .copyA 1946 1953 :=
  AXTyped.Bound.copyA 1946 (by decide) bound1946_c
theorem block1953 : AXTyped.Bound .push 1953 1972 :=
  AXTyped.Bound.push 1928 (by decide) bound1953_p
theorem block1972 : AXTyped.Bound .copyH 1972 1979 :=
  AXTyped.Bound.copyH 1972 (by decide) bound1972_c
theorem block1979 : AXTyped.Bound .cons 1979 2006 :=
  AXTyped.Bound.cons 1959 (by decide) bound1979_u bound1979_q bound1979_m
theorem block2006 : AXTyped.Bound .incT 2006 2007 :=
  AXTyped.Bound.incT 2006 (by decide) row2006_i0
theorem block2007 : AXTyped.Bound .cons 2007 2034 :=
  AXTyped.Bound.cons 1987 (by decide) bound2007_u bound2007_q bound2007_m
theorem block2034 : AXTyped.Bound .cons 2034 2061 :=
  AXTyped.Bound.cons 2014 (by decide) bound2034_u bound2034_q bound2034_m
end M6.Source.AXModelBounds

