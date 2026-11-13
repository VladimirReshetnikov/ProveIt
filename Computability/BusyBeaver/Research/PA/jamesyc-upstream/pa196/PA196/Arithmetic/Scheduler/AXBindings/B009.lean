module
public import PA196.Arithmetic.Scheduler.AXBindings.B008
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound1508_c : CopyToT.Bound Program.sites 5 1508 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1508 : AXTyped.Bound .copyH 1508 1515 :=
  .copyH 1508 (by decide) bound1508_c

private theorem bound1515_u : UnpairPartial.Bound Program.sites 1515 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1515_p : AXPair.Bound Program.sites 1495 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1515_t : AXTimes4.Bound Program.sites 1536 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1515 : AXTyped.Bound .cons 1515 1542 :=
  .cons 1495 (by decide) bound1515_u bound1515_p bound1515_t

private theorem bound1542 : resolveAt Program.sites 1542 = some (.inc 1 (some 1543)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1542 : AXTyped.Bound .incT 1542 1543 :=
  .incT 1542 (by decide) bound1542

private theorem bound1543_p : AXPushParam.Bound Program.sites 1518 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1543 : AXTyped.Bound .push 1543 1562 :=
  .push 1518 (by decide) bound1543_p

private theorem bound1562_c : CopyToT.Bound Program.sites 3 1562 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1562 : AXTyped.Bound .copyA 1562 1569 :=
  .copyA 1562 (by decide) bound1562_c

private theorem bound1569_p : AXPushParam.Bound Program.sites 1544 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1569 : AXTyped.Bound .push 1569 1588 :=
  .push 1544 (by decide) bound1569_p

private theorem bound1588_c : CopyToT.Bound Program.sites 4 1588 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1588 : AXTyped.Bound .copyD 1588 1595 :=
  .copyD 1588 (by decide) bound1588_c

private theorem bound1595_u : UnpairPartial.Bound Program.sites 1595 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1595_p : AXPair.Bound Program.sites 1575 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1595_t : AXTimes4.Bound Program.sites 1616 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1595 : AXTyped.Bound .cons 1595 1622 :=
  .cons 1575 (by decide) bound1595_u bound1595_p bound1595_t

private theorem bound1622 : resolveAt Program.sites 1622 = some (.inc 1 (some 1623)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1622 : AXTyped.Bound .incT 1622 1623 :=
  .incT 1622 (by decide) bound1622

private theorem bound1623_u : UnpairPartial.Bound Program.sites 1623 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1623_p : AXPair.Bound Program.sites 1603 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1623_t : AXTimes4.Bound Program.sites 1644 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1623 : AXTyped.Bound .cons 1623 1650 :=
  .cons 1603 (by decide) bound1623_u bound1623_p bound1623_t

private theorem bound1650_u : UnpairPartial.Bound Program.sites 1650 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1650_p : AXPair.Bound Program.sites 1630 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1650_t : AXTimes4.Bound Program.sites 1671 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1650 : AXTyped.Bound .cons 1650 1677 :=
  .cons 1630 (by decide) bound1650_u bound1650_p bound1650_t

private theorem bound1677_p : AXPushParam.Bound Program.sites 1652 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1677 : AXTyped.Bound .push 1677 1696 :=
  .push 1652 (by decide) bound1677_p

end PA196.Arithmetic.Scheduler.AXBindings
