module
public import PA196.Arithmetic.Scheduler.AXBindings.B005
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound1056 : resolveAt Program.sites 1056 = some (.inc 1 (some 1057)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1056 : AXTyped.Bound .incT 1056 1057 :=
  .incT 1056 (by decide) bound1056

private theorem bound1057 : resolveAt Program.sites 1057 = some (.inc 1 (some 1058)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1057 : AXTyped.Bound .incT 1057 1058 :=
  .incT 1057 (by decide) bound1057

private theorem bound1058_u : UnpairPartial.Bound Program.sites 1058 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1058_p : AXPair.Bound Program.sites 1038 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1058_t : AXTimes4.Bound Program.sites 1079 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1058 : AXTyped.Bound .cons 1058 1085 :=
  .cons 1038 (by decide) bound1058_u bound1058_p bound1058_t

private theorem bound1085_p : AXPushParam.Bound Program.sites 1060 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1085 : AXTyped.Bound .push 1085 1104 :=
  .push 1060 (by decide) bound1085_p

private theorem bound1104_c : CopyToT.Bound Program.sites 5 1104 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1104 : AXTyped.Bound .copyH 1104 1111 :=
  .copyH 1104 (by decide) bound1104_c

private theorem bound1111_p : AXPushParam.Bound Program.sites 1086 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1111 : AXTyped.Bound .push 1111 1130 :=
  .push 1086 (by decide) bound1111_p

private theorem bound1130_c : CopyToT.Bound Program.sites 4 1130 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1130 : AXTyped.Bound .copyD 1130 1137 :=
  .copyD 1130 (by decide) bound1130_c

private theorem bound1137_u : UnpairPartial.Bound Program.sites 1137 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1137_p : AXPair.Bound Program.sites 1117 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1137_t : AXTimes4.Bound Program.sites 1158 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1137 : AXTyped.Bound .cons 1137 1164 :=
  .cons 1117 (by decide) bound1137_u bound1137_p bound1137_t

private theorem bound1164 : resolveAt Program.sites 1164 = some (.inc 1 (some 1165)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1164 : AXTyped.Bound .incT 1164 1165 :=
  .incT 1164 (by decide) bound1164

private theorem bound1165_p : AXPushParam.Bound Program.sites 1140 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1165 : AXTyped.Bound .push 1165 1184 :=
  .push 1140 (by decide) bound1165_p

private theorem bound1184_c : CopyToT.Bound Program.sites 5 1184 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1184 : AXTyped.Bound .copyH 1184 1191 :=
  .copyH 1184 (by decide) bound1184_c

private theorem bound1191_p : AXPushParam.Bound Program.sites 1166 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1191 : AXTyped.Bound .push 1191 1210 :=
  .push 1166 (by decide) bound1191_p

end PA196.Arithmetic.Scheduler.AXBindings
