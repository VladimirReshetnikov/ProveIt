module
public import PA196.Arithmetic.Scheduler.AXBindings.B016
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound2746_p : AXPushParam.Bound Program.sites 2721 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2746 : AXTyped.Bound .push 2746 2765 :=
  .push 2721 (by decide) bound2746_p

private theorem bound2765_c : CopyToT.Bound Program.sites 5 2765 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2765 : AXTyped.Bound .copyH 2765 2772 :=
  .copyH 2765 (by decide) bound2765_c

private theorem bound2772_p : AXPushParam.Bound Program.sites 2747 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2772 : AXTyped.Bound .push 2772 2791 :=
  .push 2747 (by decide) bound2772_p

private theorem bound2791_c : CopyToT.Bound Program.sites 4 2791 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2791 : AXTyped.Bound .copyD 2791 2798 :=
  .copyD 2791 (by decide) bound2791_c

private theorem bound2798_u : UnpairPartial.Bound Program.sites 2798 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2798_p : AXPair.Bound Program.sites 2778 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2798_t : AXTimes4.Bound Program.sites 2819 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2798 : AXTyped.Bound .cons 2798 2825 :=
  .cons 2778 (by decide) bound2798_u bound2798_p bound2798_t

private theorem bound2825 : resolveAt Program.sites 2825 = some (.inc 1 (some 2826)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2825 : AXTyped.Bound .incT 2825 2826 :=
  .incT 2825 (by decide) bound2825

private theorem bound2826_p : AXPushParam.Bound Program.sites 2801 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2826 : AXTyped.Bound .push 2826 2845 :=
  .push 2801 (by decide) bound2826_p

private theorem bound2845_c : CopyToT.Bound Program.sites 3 2845 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2845 : AXTyped.Bound .copyA 2845 2852 :=
  .copyA 2845 (by decide) bound2845_c

private theorem bound2852_p : AXPushParam.Bound Program.sites 2827 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2852 : AXTyped.Bound .push 2852 2871 :=
  .push 2827 (by decide) bound2852_p

private theorem bound2871_c : CopyToT.Bound Program.sites 3 2871 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2871 : AXTyped.Bound .copyA 2871 2878 :=
  .copyA 2871 (by decide) bound2871_c

private theorem bound2878_p : AXPushParam.Bound Program.sites 2853 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2878 : AXTyped.Bound .push 2878 2897 :=
  .push 2853 (by decide) bound2878_p

private theorem bound2897_c : CopyToT.Bound Program.sites 4 2897 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2897 : AXTyped.Bound .copyD 2897 2904 :=
  .copyD 2897 (by decide) bound2897_c

end PA196.Arithmetic.Scheduler.AXBindings
