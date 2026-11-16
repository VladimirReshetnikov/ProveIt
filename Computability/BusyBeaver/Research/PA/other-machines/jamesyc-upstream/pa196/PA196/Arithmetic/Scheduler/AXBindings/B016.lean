module
public import PA196.Arithmetic.Scheduler.AXBindings.B015
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound2584_p : AXPushParam.Bound Program.sites 2559 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2584 : AXTyped.Bound .push 2584 2603 :=
  .push 2559 (by decide) bound2584_p

private theorem bound2603_c : CopyToT.Bound Program.sites 5 2603 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2603 : AXTyped.Bound .copyH 2603 2610 :=
  .copyH 2603 (by decide) bound2603_c

private theorem bound2610_p : AXPushParam.Bound Program.sites 2585 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2610 : AXTyped.Bound .push 2610 2629 :=
  .push 2585 (by decide) bound2610_p

private theorem bound2629_c : CopyToT.Bound Program.sites 4 2629 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2629 : AXTyped.Bound .copyD 2629 2636 :=
  .copyD 2629 (by decide) bound2629_c

private theorem bound2636_u : UnpairPartial.Bound Program.sites 2636 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2636_p : AXPair.Bound Program.sites 2616 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2636_t : AXTimes4.Bound Program.sites 2657 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2636 : AXTyped.Bound .cons 2636 2663 :=
  .cons 2616 (by decide) bound2636_u bound2636_p bound2636_t

private theorem bound2663 : resolveAt Program.sites 2663 = some (.inc 1 (some 2664)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2663 : AXTyped.Bound .incT 2663 2664 :=
  .incT 2663 (by decide) bound2663

private theorem bound2664_p : AXPushParam.Bound Program.sites 2639 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2664 : AXTyped.Bound .push 2664 2683 :=
  .push 2639 (by decide) bound2664_p

private theorem bound2683_c : CopyToT.Bound Program.sites 3 2683 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2683 : AXTyped.Bound .copyA 2683 2690 :=
  .copyA 2683 (by decide) bound2683_c

private theorem bound2690_u : UnpairPartial.Bound Program.sites 2690 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2690_p : AXPair.Bound Program.sites 2670 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2690_t : AXTimes4.Bound Program.sites 2711 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2690 : AXTyped.Bound .cons 2690 2717 :=
  .cons 2670 (by decide) bound2690_u bound2690_p bound2690_t

private theorem bound2717 : resolveAt Program.sites 2717 = some (.inc 1 (some 2718)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2717 : AXTyped.Bound .incT 2717 2718 :=
  .incT 2717 (by decide) bound2717

private theorem bound2718 : resolveAt Program.sites 2718 = some (.inc 1 (some 2719)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2718 : AXTyped.Bound .incT 2718 2719 :=
  .incT 2718 (by decide) bound2718

private theorem bound2719_u : UnpairPartial.Bound Program.sites 2719 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2719_p : AXPair.Bound Program.sites 2699 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2719_t : AXTimes4.Bound Program.sites 2740 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2719 : AXTyped.Bound .cons 2719 2746 :=
  .cons 2699 (by decide) bound2719_u bound2719_p bound2719_t

end PA196.Arithmetic.Scheduler.AXBindings
