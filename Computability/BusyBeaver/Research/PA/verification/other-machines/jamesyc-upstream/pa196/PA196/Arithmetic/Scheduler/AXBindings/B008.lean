module
public import PA196.Arithmetic.Scheduler.AXBindings.B007
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound1354_u : UnpairPartial.Bound Program.sites 1354 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1354_p : AXPair.Bound Program.sites 1334 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1354_t : AXTimes4.Bound Program.sites 1375 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1354 : AXTyped.Bound .cons 1354 1381 :=
  .cons 1334 (by decide) bound1354_u bound1354_p bound1354_t

private theorem bound1381_p : AXPushParam.Bound Program.sites 1356 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1381 : AXTyped.Bound .push 1381 1400 :=
  .push 1356 (by decide) bound1381_p

private theorem bound1400_c : CopyToT.Bound Program.sites 5 1400 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1400 : AXTyped.Bound .copyH 1400 1407 :=
  .copyH 1400 (by decide) bound1400_c

private theorem bound1407_p : AXPushParam.Bound Program.sites 1382 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1407 : AXTyped.Bound .push 1407 1426 :=
  .push 1382 (by decide) bound1407_p

private theorem bound1426_c : CopyToT.Bound Program.sites 4 1426 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1426 : AXTyped.Bound .copyD 1426 1433 :=
  .copyD 1426 (by decide) bound1426_c

private theorem bound1433_u : UnpairPartial.Bound Program.sites 1433 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1433_p : AXPair.Bound Program.sites 1413 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1433_t : AXTimes4.Bound Program.sites 1454 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1433 : AXTyped.Bound .cons 1433 1460 :=
  .cons 1413 (by decide) bound1433_u bound1433_p bound1433_t

private theorem bound1460 : resolveAt Program.sites 1460 = some (.inc 1 (some 1461)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1460 : AXTyped.Bound .incT 1460 1461 :=
  .incT 1460 (by decide) bound1460

private theorem bound1461 : resolveAt Program.sites 1461 = some (.inc 1 (some 1462)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1461 : AXTyped.Bound .incT 1461 1462 :=
  .incT 1461 (by decide) bound1461

private theorem bound1462 : resolveAt Program.sites 1462 = some (.inc 1 (some 1463)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1462 : AXTyped.Bound .incT 1462 1463 :=
  .incT 1462 (by decide) bound1462

private theorem bound1463_p : AXPushParam.Bound Program.sites 1438 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1463 : AXTyped.Bound .push 1463 1482 :=
  .push 1438 (by decide) bound1463_p

private theorem bound1482_c : CopyToT.Bound Program.sites 3 1482 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1482 : AXTyped.Bound .copyA 1482 1489 :=
  .copyA 1482 (by decide) bound1482_c

private theorem bound1489_p : AXPushParam.Bound Program.sites 1464 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1489 : AXTyped.Bound .push 1489 1508 :=
  .push 1464 (by decide) bound1489_p

end PA196.Arithmetic.Scheduler.AXBindings
