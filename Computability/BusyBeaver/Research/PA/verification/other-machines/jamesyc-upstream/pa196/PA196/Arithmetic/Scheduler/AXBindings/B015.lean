module
public import PA196.Arithmetic.Scheduler.AXBindings.B014
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound2422_p : AXPushParam.Bound Program.sites 2397 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2422 : AXTyped.Bound .push 2422 2441 :=
  .push 2397 (by decide) bound2422_p

private theorem bound2441_c : CopyToT.Bound Program.sites 3 2441 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2441 : AXTyped.Bound .copyA 2441 2448 :=
  .copyA 2441 (by decide) bound2441_c

private theorem bound2448_u : UnpairPartial.Bound Program.sites 2448 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2448_p : AXPair.Bound Program.sites 2428 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2448_t : AXTimes4.Bound Program.sites 2469 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2448 : AXTyped.Bound .cons 2448 2475 :=
  .cons 2428 (by decide) bound2448_u bound2448_p bound2448_t

private theorem bound2475 : resolveAt Program.sites 2475 = some (.inc 1 (some 2476)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2475 : AXTyped.Bound .incT 2475 2476 :=
  .incT 2475 (by decide) bound2475

private theorem bound2476 : resolveAt Program.sites 2476 = some (.inc 1 (some 2477)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2476 : AXTyped.Bound .incT 2476 2477 :=
  .incT 2476 (by decide) bound2476

private theorem bound2477_u : UnpairPartial.Bound Program.sites 2477 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2477_p : AXPair.Bound Program.sites 2457 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2477_t : AXTimes4.Bound Program.sites 2498 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2477 : AXTyped.Bound .cons 2477 2504 :=
  .cons 2457 (by decide) bound2477_u bound2477_p bound2477_t

private theorem bound2504_p : AXPushParam.Bound Program.sites 2479 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2504 : AXTyped.Bound .push 2504 2523 :=
  .push 2479 (by decide) bound2504_p

private theorem bound2523_c : CopyToT.Bound Program.sites 5 2523 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2523 : AXTyped.Bound .copyH 2523 2530 :=
  .copyH 2523 (by decide) bound2523_c

private theorem bound2530_p : AXPushParam.Bound Program.sites 2505 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2530 : AXTyped.Bound .push 2530 2549 :=
  .push 2505 (by decide) bound2530_p

private theorem bound2549_c : CopyToT.Bound Program.sites 4 2549 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2549 : AXTyped.Bound .copyD 2549 2556 :=
  .copyD 2549 (by decide) bound2549_c

private theorem bound2556_u : UnpairPartial.Bound Program.sites 2556 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2556_p : AXPair.Bound Program.sites 2536 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2556_t : AXTimes4.Bound Program.sites 2577 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2556 : AXTyped.Bound .cons 2556 2583 :=
  .cons 2536 (by decide) bound2556_u bound2556_p bound2556_t

private theorem bound2583 : resolveAt Program.sites 2583 = some (.inc 1 (some 2584)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2583 : AXTyped.Bound .incT 2583 2584 :=
  .incT 2583 (by decide) bound2583

end PA196.Arithmetic.Scheduler.AXBindings
