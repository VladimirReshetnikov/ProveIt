module
public import PA196.Arithmetic.Scheduler.AXBindings.B006
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound1210_c : CopyToT.Bound Program.sites 3 1210 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1210 : AXTyped.Bound .copyA 1210 1217 :=
  .copyA 1210 (by decide) bound1210_c

private theorem bound1217_u : UnpairPartial.Bound Program.sites 1217 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1217_p : AXPair.Bound Program.sites 1197 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1217_t : AXTimes4.Bound Program.sites 1238 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1217 : AXTyped.Bound .cons 1217 1244 :=
  .cons 1197 (by decide) bound1217_u bound1217_p bound1217_t

private theorem bound1244 : resolveAt Program.sites 1244 = some (.inc 1 (some 1245)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1244 : AXTyped.Bound .incT 1244 1245 :=
  .incT 1244 (by decide) bound1244

private theorem bound1245 : resolveAt Program.sites 1245 = some (.inc 1 (some 1246)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1245 : AXTyped.Bound .incT 1245 1246 :=
  .incT 1245 (by decide) bound1245

private theorem bound1246 : resolveAt Program.sites 1246 = some (.inc 1 (some 1247)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1246 : AXTyped.Bound .incT 1246 1247 :=
  .incT 1246 (by decide) bound1246

private theorem bound1247_p : AXPushParam.Bound Program.sites 1222 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1247 : AXTyped.Bound .push 1247 1266 :=
  .push 1222 (by decide) bound1247_p

private theorem bound1266_c : CopyToT.Bound Program.sites 3 1266 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1266 : AXTyped.Bound .copyA 1266 1273 :=
  .copyA 1266 (by decide) bound1266_c

private theorem bound1273_p : AXPushParam.Bound Program.sites 1248 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1273 : AXTyped.Bound .push 1273 1292 :=
  .push 1248 (by decide) bound1273_p

private theorem bound1292_c : CopyToT.Bound Program.sites 4 1292 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1292 : AXTyped.Bound .copyD 1292 1299 :=
  .copyD 1292 (by decide) bound1292_c

private theorem bound1299_u : UnpairPartial.Bound Program.sites 1299 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1299_p : AXPair.Bound Program.sites 1279 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1299_t : AXTimes4.Bound Program.sites 1320 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1299 : AXTyped.Bound .cons 1299 1326 :=
  .cons 1279 (by decide) bound1299_u bound1299_p bound1299_t

private theorem bound1326 : resolveAt Program.sites 1326 = some (.inc 1 (some 1327)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1326 : AXTyped.Bound .incT 1326 1327 :=
  .incT 1326 (by decide) bound1326

private theorem bound1327_u : UnpairPartial.Bound Program.sites 1327 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1327_p : AXPair.Bound Program.sites 1307 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1327_t : AXTimes4.Bound Program.sites 1348 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1327 : AXTyped.Bound .cons 1327 1354 :=
  .cons 1307 (by decide) bound1327_u bound1327_p bound1327_t

end PA196.Arithmetic.Scheduler.AXBindings
