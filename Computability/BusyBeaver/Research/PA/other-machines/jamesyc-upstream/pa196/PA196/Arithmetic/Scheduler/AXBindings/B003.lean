module
public import PA196.Arithmetic.Scheduler.AXBindings.B002
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound584_p : AXPushParam.Bound Program.sites 559 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block584 : AXTyped.Bound .push 584 603 :=
  .push 559 (by decide) bound584_p

private theorem bound603 : resolveAt Program.sites 603 = some (.inc 1 (some 604)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block603 : AXTyped.Bound .incT 603 604 :=
  .incT 603 (by decide) bound603

private theorem bound604_u : UnpairPartial.Bound Program.sites 604 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound604_p : AXPair.Bound Program.sites 584 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound604_t : AXTimes4.Bound Program.sites 625 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block604 : AXTyped.Bound .cons 604 631 :=
  .cons 584 (by decide) bound604_u bound604_p bound604_t

private theorem bound631_p : AXPushParam.Bound Program.sites 606 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block631 : AXTyped.Bound .push 631 650 :=
  .push 606 (by decide) bound631_p

private theorem bound650_c : CopyToT.Bound Program.sites 4 650 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block650 : AXTyped.Bound .copyD 650 657 :=
  .copyD 650 (by decide) bound650_c

private theorem bound657_u : UnpairPartial.Bound Program.sites 657 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound657_p : AXPair.Bound Program.sites 637 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound657_t : AXTimes4.Bound Program.sites 678 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block657 : AXTyped.Bound .cons 657 684 :=
  .cons 637 (by decide) bound657_u bound657_p bound657_t

private theorem bound684 : resolveAt Program.sites 684 = some (.inc 1 (some 685)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block684 : AXTyped.Bound .incT 684 685 :=
  .incT 684 (by decide) bound684

private theorem bound685 : resolveAt Program.sites 685 = some (.inc 1 (some 686)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block685 : AXTyped.Bound .incT 685 686 :=
  .incT 685 (by decide) bound685

private theorem bound686_p : AXPushParam.Bound Program.sites 661 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block686 : AXTyped.Bound .push 686 705 :=
  .push 661 (by decide) bound686_p

private theorem bound705 : resolveAt Program.sites 705 = some (.inc 1 (some 706)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block705 : AXTyped.Bound .incT 705 706 :=
  .incT 705 (by decide) bound705

private theorem bound706_u : UnpairPartial.Bound Program.sites 706 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound706_p : AXPair.Bound Program.sites 686 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound706_t : AXTimes4.Bound Program.sites 727 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block706 : AXTyped.Bound .cons 706 733 :=
  .cons 686 (by decide) bound706_u bound706_p bound706_t

private theorem bound733_p : AXPushParam.Bound Program.sites 708 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block733 : AXTyped.Bound .push 733 752 :=
  .push 708 (by decide) bound733_p

end PA196.Arithmetic.Scheduler.AXBindings
