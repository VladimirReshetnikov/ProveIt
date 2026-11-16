module
public import PA196.Source.AXBindings.B019
public import PA196.Program
public import PA196.Source.Readers
public import M6.Source.AXMacroPlan
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Source.AXBindings
open M6.Source
private theorem bound3294 : resolveAt Program.sites 3294 = some (.inc 1 (some 3295)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block3294 : AXMacro.Realizes Program.sites .incT 3294 3295 :=
  AXMacro.inc_realizes bound3294

private theorem bound3295_p : AXPushParam.Bound Program.sites 3270 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3295 : AXMacro.Realizes Program.sites .push 3295 3314 :=
  AXMacro.push_realizes bound3295_p

private theorem bound3314_c : CopyToT.Bound Program.sites 3 3314 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3314 : AXMacro.Realizes Program.sites .copyA 3314 3321 :=
  AXMacro.copyA_realizes bound3314_c

private theorem bound3321_p : AXPushParam.Bound Program.sites 3296 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3321 : AXMacro.Realizes Program.sites .push 3321 3340 :=
  AXMacro.push_realizes bound3321_p

private theorem bound3340_c : CopyToT.Bound Program.sites 3 3340 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3340 : AXMacro.Realizes Program.sites .copyA 3340 3347 :=
  AXMacro.copyA_realizes bound3340_c

private theorem bound3347_p : AXPushParam.Bound Program.sites 3322 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3347 : AXMacro.Realizes Program.sites .push 3347 3366 :=
  AXMacro.push_realizes bound3347_p

private theorem bound3366_c : CopyToT.Bound Program.sites 4 3366 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3366 : AXMacro.Realizes Program.sites .copyD 3366 3373 :=
  AXMacro.copyD_realizes bound3366_c

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
theorem block3373 : AXMacro.Realizes Program.sites .cons 3373 3400 :=
  AXMacro.cons_realizes bound3373_u bound3373_p bound3373_t

private theorem bound3400 : resolveAt Program.sites 3400 = some (.inc 1 (some 3401)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block3400 : AXMacro.Realizes Program.sites .incT 3400 3401 :=
  AXMacro.inc_realizes bound3400

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
theorem block3401 : AXMacro.Realizes Program.sites .cons 3401 3428 :=
  AXMacro.cons_realizes bound3401_u bound3401_p bound3401_t

private theorem bound3428_p : AXPushParam.Bound Program.sites 3403 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3428 : AXMacro.Realizes Program.sites .push 3428 3447 :=
  AXMacro.push_realizes bound3428_p

private theorem bound3447 : resolveAt Program.sites 3447 = some (.inc 1 (some 3448)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block3447 : AXMacro.Realizes Program.sites .incT 3447 3448 :=
  AXMacro.inc_realizes bound3447

end PA196.Source.AXBindings
