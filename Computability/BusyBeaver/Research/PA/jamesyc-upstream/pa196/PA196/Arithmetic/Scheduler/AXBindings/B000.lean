module
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound50_p : AXPushParam.Bound Program.sites 25 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block50 : AXTyped.Bound .push 50 69 :=
  .push 25 (by decide) bound50_p

private theorem bound69_c : CopyToT.Bound Program.sites 5 69 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block69 : AXTyped.Bound .copyH 69 76 :=
  .copyH 69 (by decide) bound69_c

private theorem bound76_p : AXPushParam.Bound Program.sites 51 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block76 : AXTyped.Bound .push 76 95 :=
  .push 51 (by decide) bound76_p

private theorem bound95_c : CopyToT.Bound Program.sites 4 95 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block95 : AXTyped.Bound .copyD 95 102 :=
  .copyD 95 (by decide) bound95_c

private theorem bound102_u : UnpairPartial.Bound Program.sites 102 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound102_p : AXPair.Bound Program.sites 82 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound102_t : AXTimes4.Bound Program.sites 123 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block102 : AXTyped.Bound .cons 102 129 :=
  .cons 82 (by decide) bound102_u bound102_p bound102_t

private theorem bound129 : resolveAt Program.sites 129 = some (.inc 1 (some 130)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block129 : AXTyped.Bound .incT 129 130 :=
  .incT 129 (by decide) bound129

private theorem bound130 : resolveAt Program.sites 130 = some (.inc 1 (some 131)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block130 : AXTyped.Bound .incT 130 131 :=
  .incT 130 (by decide) bound130

private theorem bound131_r : PA196.Source.Readers.Bound Program.sites (AXMacro.readerH 131) := by
  unfold PA196.Source.Readers.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block131 : AXTyped.Bound .readH 131 145 :=
  .readH 131 (by decide) bound131_r

private theorem bound145_p : AXPushParam.Bound Program.sites 120 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block145 : AXTyped.Bound .push 145 164 :=
  .push 120 (by decide) bound145_p

private theorem bound164_c : CopyToT.Bound Program.sites 5 164 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block164 : AXTyped.Bound .copyH 164 171 :=
  .copyH 164 (by decide) bound164_c

private theorem bound171_p : AXPushParam.Bound Program.sites 146 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block171 : AXTyped.Bound .push 171 190 :=
  .push 146 (by decide) bound171_p

private theorem bound190_c : CopyToT.Bound Program.sites 4 190 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block190 : AXTyped.Bound .copyD 190 197 :=
  .copyD 190 (by decide) bound190_c

end PA196.Arithmetic.Scheduler.AXBindings
