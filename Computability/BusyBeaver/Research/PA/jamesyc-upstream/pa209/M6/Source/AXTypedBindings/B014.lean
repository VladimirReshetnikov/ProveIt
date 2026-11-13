module
public import M6.Source.AXBindings.B014
import all M6.Source.AXBindings.B014
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem bound2247_u : UnpairPartial.Bound exactSites 2247 :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.bound2247_u"
theorem bound2247_q : AXPair.Bound exactSites 2227 :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.bound2247_q"
theorem bound2247_m : AXTimes4.Bound exactSites 2268 :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.bound2247_m"
theorem row2274_i0 : resolveAt exactSites 2274 = some (Instruction.inc 1 (some 2275)) :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.row2274_i0"
theorem row2275_i0 : resolveAt exactSites 2275 = some (Instruction.inc 1 (some 2276)) :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.row2275_i0"
theorem bound2276_p : AXPushParam.Bound exactSites 2251 :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.bound2276_p"
theorem bound2295_c : CopyToT.Bound exactSites 4 2295 :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.bound2295_c"
theorem bound2302_p : AXPushParam.Bound exactSites 2277 :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.bound2302_p"
theorem bound2321_c : CopyToT.Bound exactSites 3 2321 :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.bound2321_c"
theorem bound2328_u : UnpairPartial.Bound exactSites 2328 :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.bound2328_u"
theorem bound2328_q : AXPair.Bound exactSites 2308 :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.bound2328_q"
theorem bound2328_m : AXTimes4.Bound exactSites 2349 :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.bound2328_m"
theorem row2355_i0 : resolveAt exactSites 2355 = some (Instruction.inc 1 (some 2356)) :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.row2355_i0"
theorem row2356_i0 : resolveAt exactSites 2356 = some (Instruction.inc 1 (some 2357)) :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.row2356_i0"
theorem bound2357_u : UnpairPartial.Bound exactSites 2357 :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.bound2357_u"
theorem bound2357_q : AXPair.Bound exactSites 2337 :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.bound2357_q"
theorem bound2357_m : AXTimes4.Bound exactSites 2378 :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.bound2357_m"
theorem bound2384_u : UnpairPartial.Bound exactSites 2384 :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.bound2384_u"
theorem bound2384_q : AXPair.Bound exactSites 2364 :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.bound2384_q"
theorem bound2384_m : AXTimes4.Bound exactSites 2405 :=
  existingPrivateBound% "M6.Source.AXBindings.B014" "M6.Source.AXAll.bound2384_m"
theorem block2247 : AXTyped.Bound .cons 2247 2274 :=
  AXTyped.Bound.cons 2227 (by decide) bound2247_u bound2247_q bound2247_m
theorem block2274 : AXTyped.Bound .incT 2274 2275 :=
  AXTyped.Bound.incT 2274 (by decide) row2274_i0
theorem block2275 : AXTyped.Bound .incT 2275 2276 :=
  AXTyped.Bound.incT 2275 (by decide) row2275_i0
theorem block2276 : AXTyped.Bound .push 2276 2295 :=
  AXTyped.Bound.push 2251 (by decide) bound2276_p
theorem block2295 : AXTyped.Bound .copyD 2295 2302 :=
  AXTyped.Bound.copyD 2295 (by decide) bound2295_c
theorem block2302 : AXTyped.Bound .push 2302 2321 :=
  AXTyped.Bound.push 2277 (by decide) bound2302_p
theorem block2321 : AXTyped.Bound .copyA 2321 2328 :=
  AXTyped.Bound.copyA 2321 (by decide) bound2321_c
theorem block2328 : AXTyped.Bound .cons 2328 2355 :=
  AXTyped.Bound.cons 2308 (by decide) bound2328_u bound2328_q bound2328_m
theorem block2355 : AXTyped.Bound .incT 2355 2356 :=
  AXTyped.Bound.incT 2355 (by decide) row2355_i0
theorem block2356 : AXTyped.Bound .incT 2356 2357 :=
  AXTyped.Bound.incT 2356 (by decide) row2356_i0
theorem block2357 : AXTyped.Bound .cons 2357 2384 :=
  AXTyped.Bound.cons 2337 (by decide) bound2357_u bound2357_q bound2357_m
theorem block2384 : AXTyped.Bound .cons 2384 2411 :=
  AXTyped.Bound.cons 2364 (by decide) bound2384_u bound2384_q bound2384_m
end M6.Source.AXModelBounds

