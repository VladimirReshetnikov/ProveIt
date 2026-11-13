module
public import M6.Source.AXBindings.B005
import all M6.Source.AXBindings.B005
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem row831_i0 : resolveAt exactSites 831 = some (Instruction.inc 1 (some 832)) :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.row831_i0"
theorem row832_i0 : resolveAt exactSites 832 = some (Instruction.inc 1 (some 833)) :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.row832_i0"
theorem bound833_u : UnpairPartial.Bound exactSites 833 :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.bound833_u"
theorem bound833_q : AXPair.Bound exactSites 813 :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.bound833_q"
theorem bound833_m : AXTimes4.Bound exactSites 854 :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.bound833_m"
theorem bound860_u : UnpairPartial.Bound exactSites 860 :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.bound860_u"
theorem bound860_q : AXPair.Bound exactSites 840 :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.bound860_q"
theorem bound860_m : AXTimes4.Bound exactSites 881 :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.bound860_m"
theorem bound887_p : AXPushParam.Bound exactSites 862 :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.bound887_p"
theorem bound906_c : CopyToT.Bound exactSites 4 906 :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.bound906_c"
theorem bound913_p : AXPushParam.Bound exactSites 888 :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.bound913_p"
theorem bound932_c : CopyToT.Bound exactSites 4 932 :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.bound932_c"
theorem bound939_p : AXPushParam.Bound exactSites 914 :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.bound939_p"
theorem bound958_c : CopyToT.Bound exactSites 5 958 :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.bound958_c"
theorem bound965_u : UnpairPartial.Bound exactSites 965 :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.bound965_u"
theorem bound965_q : AXPair.Bound exactSites 945 :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.bound965_q"
theorem bound965_m : AXTimes4.Bound exactSites 986 :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.bound965_m"
theorem row992_i0 : resolveAt exactSites 992 = some (Instruction.inc 1 (some 993)) :=
  existingPrivateBound% "M6.Source.AXBindings.B005" "M6.Source.AXAll.row992_i0"
theorem block831 : AXTyped.Bound .incT 831 832 :=
  AXTyped.Bound.incT 831 (by decide) row831_i0
theorem block832 : AXTyped.Bound .incT 832 833 :=
  AXTyped.Bound.incT 832 (by decide) row832_i0
theorem block833 : AXTyped.Bound .cons 833 860 :=
  AXTyped.Bound.cons 813 (by decide) bound833_u bound833_q bound833_m
theorem block860 : AXTyped.Bound .cons 860 887 :=
  AXTyped.Bound.cons 840 (by decide) bound860_u bound860_q bound860_m
theorem block887 : AXTyped.Bound .push 887 906 :=
  AXTyped.Bound.push 862 (by decide) bound887_p
theorem block906 : AXTyped.Bound .copyD 906 913 :=
  AXTyped.Bound.copyD 906 (by decide) bound906_c
theorem block913 : AXTyped.Bound .push 913 932 :=
  AXTyped.Bound.push 888 (by decide) bound913_p
theorem block932 : AXTyped.Bound .copyD 932 939 :=
  AXTyped.Bound.copyD 932 (by decide) bound932_c
theorem block939 : AXTyped.Bound .push 939 958 :=
  AXTyped.Bound.push 914 (by decide) bound939_p
theorem block958 : AXTyped.Bound .copyH 958 965 :=
  AXTyped.Bound.copyH 958 (by decide) bound958_c
theorem block965 : AXTyped.Bound .cons 965 992 :=
  AXTyped.Bound.cons 945 (by decide) bound965_u bound965_q bound965_m
theorem block992 : AXTyped.Bound .incT 992 993 :=
  AXTyped.Bound.incT 992 (by decide) row992_i0
end M6.Source.AXModelBounds

