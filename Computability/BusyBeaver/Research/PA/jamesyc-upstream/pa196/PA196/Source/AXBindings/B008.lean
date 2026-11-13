module
public import PA196.Source.AXBindings.B007
public import PA196.Program
public import PA196.Source.Readers
public import M6.Source.AXMacroPlan
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Source.AXBindings
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
theorem block1354 : AXMacro.Realizes Program.sites .cons 1354 1381 :=
  AXMacro.cons_realizes bound1354_u bound1354_p bound1354_t

private theorem bound1381_p : AXPushParam.Bound Program.sites 1356 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1381 : AXMacro.Realizes Program.sites .push 1381 1400 :=
  AXMacro.push_realizes bound1381_p

private theorem bound1400_c : CopyToT.Bound Program.sites 5 1400 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1400 : AXMacro.Realizes Program.sites .copyH 1400 1407 :=
  AXMacro.copyH_realizes bound1400_c

private theorem bound1407_p : AXPushParam.Bound Program.sites 1382 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1407 : AXMacro.Realizes Program.sites .push 1407 1426 :=
  AXMacro.push_realizes bound1407_p

private theorem bound1426_c : CopyToT.Bound Program.sites 4 1426 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1426 : AXMacro.Realizes Program.sites .copyD 1426 1433 :=
  AXMacro.copyD_realizes bound1426_c

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
theorem block1433 : AXMacro.Realizes Program.sites .cons 1433 1460 :=
  AXMacro.cons_realizes bound1433_u bound1433_p bound1433_t

private theorem bound1460 : resolveAt Program.sites 1460 = some (.inc 1 (some 1461)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1460 : AXMacro.Realizes Program.sites .incT 1460 1461 :=
  AXMacro.inc_realizes bound1460

private theorem bound1461 : resolveAt Program.sites 1461 = some (.inc 1 (some 1462)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1461 : AXMacro.Realizes Program.sites .incT 1461 1462 :=
  AXMacro.inc_realizes bound1461

private theorem bound1462 : resolveAt Program.sites 1462 = some (.inc 1 (some 1463)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1462 : AXMacro.Realizes Program.sites .incT 1462 1463 :=
  AXMacro.inc_realizes bound1462

private theorem bound1463_p : AXPushParam.Bound Program.sites 1438 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1463 : AXMacro.Realizes Program.sites .push 1463 1482 :=
  AXMacro.push_realizes bound1463_p

private theorem bound1482_c : CopyToT.Bound Program.sites 3 1482 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1482 : AXMacro.Realizes Program.sites .copyA 1482 1489 :=
  AXMacro.copyA_realizes bound1482_c

private theorem bound1489_p : AXPushParam.Bound Program.sites 1464 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1489 : AXMacro.Realizes Program.sites .push 1489 1508 :=
  AXMacro.push_realizes bound1489_p

end PA196.Source.AXBindings
