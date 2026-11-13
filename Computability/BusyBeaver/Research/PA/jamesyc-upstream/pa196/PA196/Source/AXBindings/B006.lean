module
public import PA196.Source.AXBindings.B005
public import PA196.Program
public import PA196.Source.Readers
public import M6.Source.AXMacroPlan
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Source.AXBindings
open M6.Source
private theorem bound1056 : resolveAt Program.sites 1056 = some (.inc 1 (some 1057)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1056 : AXMacro.Realizes Program.sites .incT 1056 1057 :=
  AXMacro.inc_realizes bound1056

private theorem bound1057 : resolveAt Program.sites 1057 = some (.inc 1 (some 1058)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1057 : AXMacro.Realizes Program.sites .incT 1057 1058 :=
  AXMacro.inc_realizes bound1057

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
theorem block1058 : AXMacro.Realizes Program.sites .cons 1058 1085 :=
  AXMacro.cons_realizes bound1058_u bound1058_p bound1058_t

private theorem bound1085_p : AXPushParam.Bound Program.sites 1060 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1085 : AXMacro.Realizes Program.sites .push 1085 1104 :=
  AXMacro.push_realizes bound1085_p

private theorem bound1104_c : CopyToT.Bound Program.sites 5 1104 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1104 : AXMacro.Realizes Program.sites .copyH 1104 1111 :=
  AXMacro.copyH_realizes bound1104_c

private theorem bound1111_p : AXPushParam.Bound Program.sites 1086 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1111 : AXMacro.Realizes Program.sites .push 1111 1130 :=
  AXMacro.push_realizes bound1111_p

private theorem bound1130_c : CopyToT.Bound Program.sites 4 1130 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1130 : AXMacro.Realizes Program.sites .copyD 1130 1137 :=
  AXMacro.copyD_realizes bound1130_c

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
theorem block1137 : AXMacro.Realizes Program.sites .cons 1137 1164 :=
  AXMacro.cons_realizes bound1137_u bound1137_p bound1137_t

private theorem bound1164 : resolveAt Program.sites 1164 = some (.inc 1 (some 1165)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1164 : AXMacro.Realizes Program.sites .incT 1164 1165 :=
  AXMacro.inc_realizes bound1164

private theorem bound1165_p : AXPushParam.Bound Program.sites 1140 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1165 : AXMacro.Realizes Program.sites .push 1165 1184 :=
  AXMacro.push_realizes bound1165_p

private theorem bound1184_c : CopyToT.Bound Program.sites 5 1184 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1184 : AXMacro.Realizes Program.sites .copyH 1184 1191 :=
  AXMacro.copyH_realizes bound1184_c

private theorem bound1191_p : AXPushParam.Bound Program.sites 1166 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1191 : AXMacro.Realizes Program.sites .push 1191 1210 :=
  AXMacro.push_realizes bound1191_p

end PA196.Source.AXBindings
