module
public import PA196.Source.AXBindings.B001
public import PA196.Program
public import PA196.Source.Readers
public import M6.Source.AXMacroPlan
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Source.AXBindings
open M6.Source
private theorem bound396_p : AXPushParam.Bound Program.sites 371 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block396 : AXMacro.Realizes Program.sites .push 396 415 :=
  AXMacro.push_realizes bound396_p

private theorem bound415_c : CopyToT.Bound Program.sites 5 415 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block415 : AXMacro.Realizes Program.sites .copyH 415 422 :=
  AXMacro.copyH_realizes bound415_c

private theorem bound422_u : UnpairPartial.Bound Program.sites 422 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound422_p : AXPair.Bound Program.sites 402 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound422_t : AXTimes4.Bound Program.sites 443 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block422 : AXMacro.Realizes Program.sites .cons 422 449 :=
  AXMacro.cons_realizes bound422_u bound422_p bound422_t

private theorem bound449_u : UnpairPartial.Bound Program.sites 449 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound449_p : AXPair.Bound Program.sites 429 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound449_t : AXTimes4.Bound Program.sites 470 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block449 : AXMacro.Realizes Program.sites .cons 449 476 :=
  AXMacro.cons_realizes bound449_u bound449_p bound449_t

private theorem bound476_u : UnpairPartial.Bound Program.sites 476 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound476_p : AXPair.Bound Program.sites 456 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound476_t : AXTimes4.Bound Program.sites 497 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block476 : AXMacro.Realizes Program.sites .cons 476 503 :=
  AXMacro.cons_realizes bound476_u bound476_p bound476_t

private theorem bound503_p : AXPushParam.Bound Program.sites 478 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block503 : AXMacro.Realizes Program.sites .push 503 522 :=
  AXMacro.push_realizes bound503_p

private theorem bound522_c : CopyToT.Bound Program.sites 5 522 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block522 : AXMacro.Realizes Program.sites .copyH 522 529 :=
  AXMacro.copyH_realizes bound522_c

private theorem bound529_p : AXPushParam.Bound Program.sites 504 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block529 : AXMacro.Realizes Program.sites .push 529 548 :=
  AXMacro.push_realizes bound529_p

private theorem bound548_c : CopyToT.Bound Program.sites 4 548 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block548 : AXMacro.Realizes Program.sites .copyD 548 555 :=
  AXMacro.copyD_realizes bound548_c

private theorem bound555_u : UnpairPartial.Bound Program.sites 555 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound555_p : AXPair.Bound Program.sites 535 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound555_t : AXTimes4.Bound Program.sites 576 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block555 : AXMacro.Realizes Program.sites .cons 555 582 :=
  AXMacro.cons_realizes bound555_u bound555_p bound555_t

private theorem bound582 : resolveAt Program.sites 582 = some (.inc 1 (some 583)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block582 : AXMacro.Realizes Program.sites .incT 582 583 :=
  AXMacro.inc_realizes bound582

private theorem bound583 : resolveAt Program.sites 583 = some (.inc 1 (some 584)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block583 : AXMacro.Realizes Program.sites .incT 583 584 :=
  AXMacro.inc_realizes bound583

end PA196.Source.AXBindings
