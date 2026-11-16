module
public import PA196.Arithmetic.Scheduler.AXBindings.B001
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound396_p : AXPushParam.Bound Program.sites 371 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block396 : AXTyped.Bound .push 396 415 :=
  .push 371 (by decide) bound396_p

private theorem bound415_c : CopyToT.Bound Program.sites 5 415 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block415 : AXTyped.Bound .copyH 415 422 :=
  .copyH 415 (by decide) bound415_c

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
theorem block422 : AXTyped.Bound .cons 422 449 :=
  .cons 402 (by decide) bound422_u bound422_p bound422_t

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
theorem block449 : AXTyped.Bound .cons 449 476 :=
  .cons 429 (by decide) bound449_u bound449_p bound449_t

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
theorem block476 : AXTyped.Bound .cons 476 503 :=
  .cons 456 (by decide) bound476_u bound476_p bound476_t

private theorem bound503_p : AXPushParam.Bound Program.sites 478 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block503 : AXTyped.Bound .push 503 522 :=
  .push 478 (by decide) bound503_p

private theorem bound522_c : CopyToT.Bound Program.sites 5 522 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block522 : AXTyped.Bound .copyH 522 529 :=
  .copyH 522 (by decide) bound522_c

private theorem bound529_p : AXPushParam.Bound Program.sites 504 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block529 : AXTyped.Bound .push 529 548 :=
  .push 504 (by decide) bound529_p

private theorem bound548_c : CopyToT.Bound Program.sites 4 548 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block548 : AXTyped.Bound .copyD 548 555 :=
  .copyD 548 (by decide) bound548_c

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
theorem block555 : AXTyped.Bound .cons 555 582 :=
  .cons 535 (by decide) bound555_u bound555_p bound555_t

private theorem bound582 : resolveAt Program.sites 582 = some (.inc 1 (some 583)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block582 : AXTyped.Bound .incT 582 583 :=
  .incT 582 (by decide) bound582

private theorem bound583 : resolveAt Program.sites 583 = some (.inc 1 (some 584)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block583 : AXTyped.Bound .incT 583 584 :=
  .incT 583 (by decide) bound583

end PA196.Arithmetic.Scheduler.AXBindings
