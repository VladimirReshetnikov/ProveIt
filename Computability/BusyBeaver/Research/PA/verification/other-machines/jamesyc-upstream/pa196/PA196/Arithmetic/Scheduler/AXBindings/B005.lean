module
public import PA196.Arithmetic.Scheduler.AXBindings.B004
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound920 : resolveAt Program.sites 920 = some (.inc 1 (some 921)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block920 : AXTyped.Bound .incT 920 921 :=
  .incT 920 (by decide) bound920

private theorem bound921 : resolveAt Program.sites 921 = some (.inc 1 (some 922)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block921 : AXTyped.Bound .incT 921 922 :=
  .incT 921 (by decide) bound921

private theorem bound922_p : AXPushParam.Bound Program.sites 897 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block922 : AXTyped.Bound .push 922 941 :=
  .push 897 (by decide) bound922_p

private theorem bound941_c : CopyToT.Bound Program.sites 5 941 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block941 : AXTyped.Bound .copyH 941 948 :=
  .copyH 941 (by decide) bound941_c

private theorem bound948_p : AXPushParam.Bound Program.sites 923 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block948 : AXTyped.Bound .push 948 967 :=
  .push 923 (by decide) bound948_p

private theorem bound967_c : CopyToT.Bound Program.sites 4 967 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block967 : AXTyped.Bound .copyD 967 974 :=
  .copyD 967 (by decide) bound967_c

private theorem bound974_u : UnpairPartial.Bound Program.sites 974 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound974_p : AXPair.Bound Program.sites 954 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound974_t : AXTimes4.Bound Program.sites 995 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block974 : AXTyped.Bound .cons 974 1001 :=
  .cons 954 (by decide) bound974_u bound974_p bound974_t

private theorem bound1001 : resolveAt Program.sites 1001 = some (.inc 1 (some 1002)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1001 : AXTyped.Bound .incT 1001 1002 :=
  .incT 1001 (by decide) bound1001

private theorem bound1002 : resolveAt Program.sites 1002 = some (.inc 1 (some 1003)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1002 : AXTyped.Bound .incT 1002 1003 :=
  .incT 1002 (by decide) bound1002

private theorem bound1003_p : AXPushParam.Bound Program.sites 978 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1003 : AXTyped.Bound .push 1003 1022 :=
  .push 978 (by decide) bound1003_p

private theorem bound1022_c : CopyToT.Bound Program.sites 3 1022 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1022 : AXTyped.Bound .copyA 1022 1029 :=
  .copyA 1022 (by decide) bound1022_c

private theorem bound1029_u : UnpairPartial.Bound Program.sites 1029 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1029_p : AXPair.Bound Program.sites 1009 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1029_t : AXTimes4.Bound Program.sites 1050 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1029 : AXTyped.Bound .cons 1029 1056 :=
  .cons 1009 (by decide) bound1029_u bound1029_p bound1029_t

end PA196.Arithmetic.Scheduler.AXBindings
