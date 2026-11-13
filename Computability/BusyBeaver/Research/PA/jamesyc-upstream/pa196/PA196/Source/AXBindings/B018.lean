module
public import PA196.Source.AXBindings.B017
public import PA196.Program
public import PA196.Source.Readers
public import M6.Source.AXMacroPlan
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Source.AXBindings
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
theorem block2904 : AXMacro.Realizes Program.sites .cons 2904 2931 :=
  AXMacro.cons_realizes bound2904_u bound2904_p bound2904_t

private theorem bound2931 : resolveAt Program.sites 2931 = some (.inc 1 (some 2932)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2931 : AXMacro.Realizes Program.sites .incT 2931 2932 :=
  AXMacro.inc_realizes bound2931

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
theorem block2932 : AXMacro.Realizes Program.sites .cons 2932 2959 :=
  AXMacro.cons_realizes bound2932_u bound2932_p bound2932_t

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
theorem block2959 : AXMacro.Realizes Program.sites .cons 2959 2986 :=
  AXMacro.cons_realizes bound2959_u bound2959_p bound2959_t

private theorem bound2986_p : AXPushParam.Bound Program.sites 2961 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2986 : AXMacro.Realizes Program.sites .push 2986 3005 :=
  AXMacro.push_realizes bound2986_p

private theorem bound3005_c : CopyToT.Bound Program.sites 3 3005 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3005 : AXMacro.Realizes Program.sites .copyA 3005 3012 :=
  AXMacro.copyA_realizes bound3005_c

private theorem bound3012_p : AXPushParam.Bound Program.sites 2987 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3012 : AXMacro.Realizes Program.sites .push 3012 3031 :=
  AXMacro.push_realizes bound3012_p

private theorem bound3031_c : CopyToT.Bound Program.sites 4 3031 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3031 : AXMacro.Realizes Program.sites .copyD 3031 3038 :=
  AXMacro.copyD_realizes bound3031_c

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
theorem block3038 : AXMacro.Realizes Program.sites .cons 3038 3065 :=
  AXMacro.cons_realizes bound3038_u bound3038_p bound3038_t

private theorem bound3065 : resolveAt Program.sites 3065 = some (.inc 1 (some 3066)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block3065 : AXMacro.Realizes Program.sites .incT 3065 3066 :=
  AXMacro.inc_realizes bound3065

private theorem bound3066_p : AXPushParam.Bound Program.sites 3041 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3066 : AXMacro.Realizes Program.sites .push 3066 3085 :=
  AXMacro.push_realizes bound3066_p

private theorem bound3085_c : CopyToT.Bound Program.sites 3 3085 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3085 : AXMacro.Realizes Program.sites .copyA 3085 3092 :=
  AXMacro.copyA_realizes bound3085_c

end PA196.Source.AXBindings
