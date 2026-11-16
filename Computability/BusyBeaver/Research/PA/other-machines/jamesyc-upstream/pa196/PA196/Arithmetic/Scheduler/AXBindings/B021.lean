module
public import PA196.Arithmetic.Scheduler.AXBindings.B020
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound3448_u : UnpairPartial.Bound Program.sites 3448 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3448_p : AXPair.Bound Program.sites 3428 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3448_t : AXTimes4.Bound Program.sites 3469 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3448 : AXTyped.Bound .cons 3448 3475 :=
  .cons 3428 (by decide) bound3448_u bound3448_p bound3448_t

private theorem bound3475_u : UnpairPartial.Bound Program.sites 3475 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3475_p : AXPair.Bound Program.sites 3455 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3475_t : AXTimes4.Bound Program.sites 3496 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3475 : AXTyped.Bound .cons 3475 3502 :=
  .cons 3455 (by decide) bound3475_u bound3475_p bound3475_t

private theorem bound3502_p : AXPushParam.Bound Program.sites 3477 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3502 : AXTyped.Bound .push 3502 3521 :=
  .push 3477 (by decide) bound3502_p

private theorem bound3521_c : CopyToT.Bound Program.sites 3 3521 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3521 : AXTyped.Bound .copyA 3521 3528 :=
  .copyA 3521 (by decide) bound3521_c

private theorem bound3528_u : UnpairPartial.Bound Program.sites 3528 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3528_p : AXPair.Bound Program.sites 3508 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3528_t : AXTimes4.Bound Program.sites 3549 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3528 : AXTyped.Bound .cons 3528 3555 :=
  .cons 3508 (by decide) bound3528_u bound3528_p bound3528_t

private theorem bound3555 : resolveAt Program.sites 3555 = some (.inc 1 (some 3556)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block3555 : AXTyped.Bound .incT 3555 3556 :=
  .incT 3555 (by decide) bound3555

private theorem bound3556 : resolveAt Program.sites 3556 = some (.inc 1 (some 3557)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block3556 : AXTyped.Bound .incT 3556 3557 :=
  .incT 3556 (by decide) bound3556

private theorem bound3557_u : UnpairPartial.Bound Program.sites 3557 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3557_p : AXPair.Bound Program.sites 3537 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3557_t : AXTimes4.Bound Program.sites 3578 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3557 : AXTyped.Bound .cons 3557 3584 :=
  .cons 3537 (by decide) bound3557_u bound3557_p bound3557_t

private theorem bound3584_u : UnpairPartial.Bound Program.sites 3584 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3584_p : AXPair.Bound Program.sites 3564 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3584_t : AXTimes4.Bound Program.sites 3605 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3584 : AXTyped.Bound .cons 3584 3611 :=
  .cons 3564 (by decide) bound3584_u bound3584_p bound3584_t

private theorem bound3611_p : AXPushParam.Bound Program.sites 3586 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3611 : AXTyped.Bound .push 3611 3630 :=
  .push 3586 (by decide) bound3611_p

private theorem bound3630 : resolveAt Program.sites 3630 = some (.inc 1 (some 3631)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block3630 : AXTyped.Bound .incT 3630 3631 :=
  .incT 3630 (by decide) bound3630

private theorem bound3631_u : UnpairPartial.Bound Program.sites 3631 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3631_p : AXPair.Bound Program.sites 3611 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3631_t : AXTimes4.Bound Program.sites 3652 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3631 : AXTyped.Bound .cons 3631 3658 :=
  .cons 3611 (by decide) bound3631_u bound3631_p bound3631_t

end PA196.Arithmetic.Scheduler.AXBindings
