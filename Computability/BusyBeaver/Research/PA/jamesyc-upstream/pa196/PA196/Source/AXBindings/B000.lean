module
public import PA196.Program
public import PA196.Source.Readers
public import M6.Source.AXMacroPlan
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Source.AXBindings
open M6.Source
private theorem bound50_p : AXPushParam.Bound Program.sites 25 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block50 : AXMacro.Realizes Program.sites .push 50 69 :=
  AXMacro.push_realizes bound50_p

private theorem bound69_c : CopyToT.Bound Program.sites 5 69 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block69 : AXMacro.Realizes Program.sites .copyH 69 76 :=
  AXMacro.copyH_realizes bound69_c

private theorem bound76_p : AXPushParam.Bound Program.sites 51 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block76 : AXMacro.Realizes Program.sites .push 76 95 :=
  AXMacro.push_realizes bound76_p

private theorem bound95_c : CopyToT.Bound Program.sites 4 95 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block95 : AXMacro.Realizes Program.sites .copyD 95 102 :=
  AXMacro.copyD_realizes bound95_c

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
theorem block102 : AXMacro.Realizes Program.sites .cons 102 129 :=
  AXMacro.cons_realizes bound102_u bound102_p bound102_t

private theorem bound129 : resolveAt Program.sites 129 = some (.inc 1 (some 130)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block129 : AXMacro.Realizes Program.sites .incT 129 130 :=
  AXMacro.inc_realizes bound129

private theorem bound130 : resolveAt Program.sites 130 = some (.inc 1 (some 131)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block130 : AXMacro.Realizes Program.sites .incT 130 131 :=
  AXMacro.inc_realizes bound130

private theorem bound131_r : Readers.Bound Program.sites (AXMacro.readerH 131) := by
  unfold Readers.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block131 : AXMacro.Realizes Program.sites .readH 131 145 :=
  Readers.readH_realizes 131 bound131_r

private theorem bound145_p : AXPushParam.Bound Program.sites 120 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block145 : AXMacro.Realizes Program.sites .push 145 164 :=
  AXMacro.push_realizes bound145_p

private theorem bound164_c : CopyToT.Bound Program.sites 5 164 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block164 : AXMacro.Realizes Program.sites .copyH 164 171 :=
  AXMacro.copyH_realizes bound164_c

private theorem bound171_p : AXPushParam.Bound Program.sites 146 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block171 : AXMacro.Realizes Program.sites .push 171 190 :=
  AXMacro.push_realizes bound171_p

private theorem bound190_c : CopyToT.Bound Program.sites 4 190 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block190 : AXMacro.Realizes Program.sites .copyD 190 197 :=
  AXMacro.copyD_realizes bound190_c

end PA196.Source.AXBindings
