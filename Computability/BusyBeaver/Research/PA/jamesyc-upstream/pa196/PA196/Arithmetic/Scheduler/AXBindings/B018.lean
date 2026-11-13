module
public import PA196.Arithmetic.Scheduler.AXBindings.B017
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound2904_u : UnpairPartial.Bound Program.sites 2904 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2904_p : AXPair.Bound Program.sites 2884 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2904_t : AXTimes4.Bound Program.sites 2925 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2904 : AXTyped.Bound .cons 2904 2931 :=
  .cons 2884 (by decide) bound2904_u bound2904_p bound2904_t

private theorem bound2931 : resolveAt Program.sites 2931 = some (.inc 1 (some 2932)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2931 : AXTyped.Bound .incT 2931 2932 :=
  .incT 2931 (by decide) bound2931

private theorem bound2932_u : UnpairPartial.Bound Program.sites 2932 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2932_p : AXPair.Bound Program.sites 2912 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2932_t : AXTimes4.Bound Program.sites 2953 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2932 : AXTyped.Bound .cons 2932 2959 :=
  .cons 2912 (by decide) bound2932_u bound2932_p bound2932_t

private theorem bound2959_u : UnpairPartial.Bound Program.sites 2959 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2959_p : AXPair.Bound Program.sites 2939 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2959_t : AXTimes4.Bound Program.sites 2980 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2959 : AXTyped.Bound .cons 2959 2986 :=
  .cons 2939 (by decide) bound2959_u bound2959_p bound2959_t

private theorem bound2986_p : AXPushParam.Bound Program.sites 2961 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2986 : AXTyped.Bound .push 2986 3005 :=
  .push 2961 (by decide) bound2986_p

private theorem bound3005_c : CopyToT.Bound Program.sites 3 3005 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3005 : AXTyped.Bound .copyA 3005 3012 :=
  .copyA 3005 (by decide) bound3005_c

private theorem bound3012_p : AXPushParam.Bound Program.sites 2987 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3012 : AXTyped.Bound .push 3012 3031 :=
  .push 2987 (by decide) bound3012_p

private theorem bound3031_c : CopyToT.Bound Program.sites 4 3031 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3031 : AXTyped.Bound .copyD 3031 3038 :=
  .copyD 3031 (by decide) bound3031_c

private theorem bound3038_u : UnpairPartial.Bound Program.sites 3038 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3038_p : AXPair.Bound Program.sites 3018 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3038_t : AXTimes4.Bound Program.sites 3059 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3038 : AXTyped.Bound .cons 3038 3065 :=
  .cons 3018 (by decide) bound3038_u bound3038_p bound3038_t

private theorem bound3065 : resolveAt Program.sites 3065 = some (.inc 1 (some 3066)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block3065 : AXTyped.Bound .incT 3065 3066 :=
  .incT 3065 (by decide) bound3065

private theorem bound3066_p : AXPushParam.Bound Program.sites 3041 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3066 : AXTyped.Bound .push 3066 3085 :=
  .push 3041 (by decide) bound3066_p

private theorem bound3085_c : CopyToT.Bound Program.sites 3 3085 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3085 : AXTyped.Bound .copyA 3085 3092 :=
  .copyA 3085 (by decide) bound3085_c

end PA196.Arithmetic.Scheduler.AXBindings
