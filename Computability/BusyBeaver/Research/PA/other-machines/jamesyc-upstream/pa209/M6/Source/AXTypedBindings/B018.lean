module
public import M6.Source.AXBindings.B018
import all M6.Source.AXBindings.B018
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem bound2857_u : UnpairPartial.Bound exactSites 2857 :=
  existingPrivateBound% "M6.Source.AXBindings.B018" "M6.Source.AXAll.bound2857_u"
theorem bound2857_q : AXPair.Bound exactSites 2837 :=
  existingPrivateBound% "M6.Source.AXBindings.B018" "M6.Source.AXAll.bound2857_q"
theorem bound2857_m : AXTimes4.Bound exactSites 2878 :=
  existingPrivateBound% "M6.Source.AXBindings.B018" "M6.Source.AXAll.bound2857_m"
theorem bound2884_p : AXPushParam.Bound exactSites 2859 :=
  existingPrivateBound% "M6.Source.AXBindings.B018" "M6.Source.AXAll.bound2884_p"
theorem bound2903_c : CopyToT.Bound exactSites 3 2903 :=
  existingPrivateBound% "M6.Source.AXBindings.B018" "M6.Source.AXAll.bound2903_c"
theorem bound2910_p : AXPushParam.Bound exactSites 2885 :=
  existingPrivateBound% "M6.Source.AXBindings.B018" "M6.Source.AXAll.bound2910_p"
theorem bound2929_c : CopyToT.Bound exactSites 5 2929 :=
  existingPrivateBound% "M6.Source.AXBindings.B018" "M6.Source.AXAll.bound2929_c"
theorem bound2936_p : AXPushParam.Bound exactSites 2911 :=
  existingPrivateBound% "M6.Source.AXBindings.B018" "M6.Source.AXAll.bound2936_p"
theorem bound2955_c : CopyToT.Bound exactSites 4 2955 :=
  existingPrivateBound% "M6.Source.AXBindings.B018" "M6.Source.AXAll.bound2955_c"
theorem bound2962_p : AXPushParam.Bound exactSites 2937 :=
  existingPrivateBound% "M6.Source.AXBindings.B018" "M6.Source.AXAll.bound2962_p"
theorem bound2981_c : CopyToT.Bound exactSites 5 2981 :=
  existingPrivateBound% "M6.Source.AXBindings.B018" "M6.Source.AXAll.bound2981_c"
theorem bound2988_u : UnpairPartial.Bound exactSites 2988 :=
  existingPrivateBound% "M6.Source.AXBindings.B018" "M6.Source.AXAll.bound2988_u"
theorem bound2988_q : AXPair.Bound exactSites 2968 :=
  existingPrivateBound% "M6.Source.AXBindings.B018" "M6.Source.AXAll.bound2988_q"
theorem bound2988_m : AXTimes4.Bound exactSites 3009 :=
  existingPrivateBound% "M6.Source.AXBindings.B018" "M6.Source.AXAll.bound2988_m"
theorem row3015_i0 : resolveAt exactSites 3015 = some (Instruction.inc 1 (some 3016)) :=
  existingPrivateBound% "M6.Source.AXBindings.B018" "M6.Source.AXAll.row3015_i0"
theorem bound3016_p : AXPushParam.Bound exactSites 2991 :=
  existingPrivateBound% "M6.Source.AXBindings.B018" "M6.Source.AXAll.bound3016_p"
theorem block2857 : AXTyped.Bound .cons 2857 2884 :=
  AXTyped.Bound.cons 2837 (by decide) bound2857_u bound2857_q bound2857_m
theorem block2884 : AXTyped.Bound .push 2884 2903 :=
  AXTyped.Bound.push 2859 (by decide) bound2884_p
theorem block2903 : AXTyped.Bound .copyA 2903 2910 :=
  AXTyped.Bound.copyA 2903 (by decide) bound2903_c
theorem block2910 : AXTyped.Bound .push 2910 2929 :=
  AXTyped.Bound.push 2885 (by decide) bound2910_p
theorem block2929 : AXTyped.Bound .copyH 2929 2936 :=
  AXTyped.Bound.copyH 2929 (by decide) bound2929_c
theorem block2936 : AXTyped.Bound .push 2936 2955 :=
  AXTyped.Bound.push 2911 (by decide) bound2936_p
theorem block2955 : AXTyped.Bound .copyD 2955 2962 :=
  AXTyped.Bound.copyD 2955 (by decide) bound2955_c
theorem block2962 : AXTyped.Bound .push 2962 2981 :=
  AXTyped.Bound.push 2937 (by decide) bound2962_p
theorem block2981 : AXTyped.Bound .copyH 2981 2988 :=
  AXTyped.Bound.copyH 2981 (by decide) bound2981_c
theorem block2988 : AXTyped.Bound .cons 2988 3015 :=
  AXTyped.Bound.cons 2968 (by decide) bound2988_u bound2988_q bound2988_m
theorem block3015 : AXTyped.Bound .incT 3015 3016 :=
  AXTyped.Bound.incT 3015 (by decide) row3015_i0
theorem block3016 : AXTyped.Bound .push 3016 3035 :=
  AXTyped.Bound.push 2991 (by decide) bound3016_p
end M6.Source.AXModelBounds

