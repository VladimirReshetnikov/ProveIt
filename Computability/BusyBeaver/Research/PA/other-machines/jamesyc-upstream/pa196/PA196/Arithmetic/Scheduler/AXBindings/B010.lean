module
public import PA196.Arithmetic.Scheduler.AXBindings.B009
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound1696_c : CopyToT.Bound Program.sites 5 1696 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1696 : AXTyped.Bound .copyH 1696 1703 :=
  .copyH 1696 (by decide) bound1696_c

private theorem bound1703_p : AXPushParam.Bound Program.sites 1678 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1703 : AXTyped.Bound .push 1703 1722 :=
  .push 1678 (by decide) bound1703_p

private theorem bound1722_c : CopyToT.Bound Program.sites 4 1722 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1722 : AXTyped.Bound .copyD 1722 1729 :=
  .copyD 1722 (by decide) bound1722_c

private theorem bound1729_u : UnpairPartial.Bound Program.sites 1729 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1729_p : AXPair.Bound Program.sites 1709 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1729_t : AXTimes4.Bound Program.sites 1750 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1729 : AXTyped.Bound .cons 1729 1756 :=
  .cons 1709 (by decide) bound1729_u bound1729_p bound1729_t

private theorem bound1756 : resolveAt Program.sites 1756 = some (.inc 1 (some 1757)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1756 : AXTyped.Bound .incT 1756 1757 :=
  .incT 1756 (by decide) bound1756

private theorem bound1757 : resolveAt Program.sites 1757 = some (.inc 1 (some 1758)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1757 : AXTyped.Bound .incT 1757 1758 :=
  .incT 1757 (by decide) bound1757

private theorem bound1758 : resolveAt Program.sites 1758 = some (.inc 1 (some 1759)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1758 : AXTyped.Bound .incT 1758 1759 :=
  .incT 1758 (by decide) bound1758

private theorem bound1759_p : AXPushParam.Bound Program.sites 1734 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1759 : AXTyped.Bound .push 1759 1778 :=
  .push 1734 (by decide) bound1759_p

private theorem bound1778 : resolveAt Program.sites 1778 = some (.inc 1 (some 1779)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1778 : AXTyped.Bound .incT 1778 1779 :=
  .incT 1778 (by decide) bound1778

private theorem bound1779_u : UnpairPartial.Bound Program.sites 1779 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1779_p : AXPair.Bound Program.sites 1759 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1779_t : AXTimes4.Bound Program.sites 1800 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1779 : AXTyped.Bound .cons 1779 1806 :=
  .cons 1759 (by decide) bound1779_u bound1779_p bound1779_t

private theorem bound1806_p : AXPushParam.Bound Program.sites 1781 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1806 : AXTyped.Bound .push 1806 1825 :=
  .push 1781 (by decide) bound1806_p

private theorem bound1825_c : CopyToT.Bound Program.sites 4 1825 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1825 : AXTyped.Bound .copyD 1825 1832 :=
  .copyD 1825 (by decide) bound1825_c

end PA196.Arithmetic.Scheduler.AXBindings
