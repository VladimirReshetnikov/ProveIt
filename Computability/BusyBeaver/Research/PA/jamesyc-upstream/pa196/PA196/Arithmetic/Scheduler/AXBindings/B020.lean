module
public import PA196.Arithmetic.Scheduler.AXBindings.B019
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound3294 : resolveAt Program.sites 3294 = some (.inc 1 (some 3295)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block3294 : AXTyped.Bound .incT 3294 3295 :=
  .incT 3294 (by decide) bound3294

private theorem bound3295_p : AXPushParam.Bound Program.sites 3270 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3295 : AXTyped.Bound .push 3295 3314 :=
  .push 3270 (by decide) bound3295_p

private theorem bound3314_c : CopyToT.Bound Program.sites 3 3314 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3314 : AXTyped.Bound .copyA 3314 3321 :=
  .copyA 3314 (by decide) bound3314_c

private theorem bound3321_p : AXPushParam.Bound Program.sites 3296 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3321 : AXTyped.Bound .push 3321 3340 :=
  .push 3296 (by decide) bound3321_p

private theorem bound3340_c : CopyToT.Bound Program.sites 3 3340 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3340 : AXTyped.Bound .copyA 3340 3347 :=
  .copyA 3340 (by decide) bound3340_c

private theorem bound3347_p : AXPushParam.Bound Program.sites 3322 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3347 : AXTyped.Bound .push 3347 3366 :=
  .push 3322 (by decide) bound3347_p

private theorem bound3366_c : CopyToT.Bound Program.sites 4 3366 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3366 : AXTyped.Bound .copyD 3366 3373 :=
  .copyD 3366 (by decide) bound3366_c

private theorem bound3373_u : UnpairPartial.Bound Program.sites 3373 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3373_p : AXPair.Bound Program.sites 3353 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3373_t : AXTimes4.Bound Program.sites 3394 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3373 : AXTyped.Bound .cons 3373 3400 :=
  .cons 3353 (by decide) bound3373_u bound3373_p bound3373_t

private theorem bound3400 : resolveAt Program.sites 3400 = some (.inc 1 (some 3401)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block3400 : AXTyped.Bound .incT 3400 3401 :=
  .incT 3400 (by decide) bound3400

private theorem bound3401_u : UnpairPartial.Bound Program.sites 3401 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3401_p : AXPair.Bound Program.sites 3381 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3401_t : AXTimes4.Bound Program.sites 3422 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3401 : AXTyped.Bound .cons 3401 3428 :=
  .cons 3381 (by decide) bound3401_u bound3401_p bound3401_t

private theorem bound3428_p : AXPushParam.Bound Program.sites 3403 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3428 : AXTyped.Bound .push 3428 3447 :=
  .push 3403 (by decide) bound3428_p

private theorem bound3447 : resolveAt Program.sites 3447 = some (.inc 1 (some 3448)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block3447 : AXTyped.Bound .incT 3447 3448 :=
  .incT 3447 (by decide) bound3447

end PA196.Arithmetic.Scheduler.AXBindings
