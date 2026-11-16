module
public import PA196.Source.AXBindings.B014
public import PA196.Program
public import PA196.Source.Readers
public import M6.Source.AXMacroPlan
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Source.AXBindings
open M6.Source
private theorem bound2422_p : AXPushParam.Bound Program.sites 2397 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2422 : AXMacro.Realizes Program.sites .push 2422 2441 :=
  AXMacro.push_realizes bound2422_p

private theorem bound2441_c : CopyToT.Bound Program.sites 3 2441 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2441 : AXMacro.Realizes Program.sites .copyA 2441 2448 :=
  AXMacro.copyA_realizes bound2441_c

private theorem bound2448_u : UnpairPartial.Bound Program.sites 2448 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2448_p : AXPair.Bound Program.sites 2428 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2448_t : AXTimes4.Bound Program.sites 2469 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2448 : AXMacro.Realizes Program.sites .cons 2448 2475 :=
  AXMacro.cons_realizes bound2448_u bound2448_p bound2448_t

private theorem bound2475 : resolveAt Program.sites 2475 = some (.inc 1 (some 2476)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2475 : AXMacro.Realizes Program.sites .incT 2475 2476 :=
  AXMacro.inc_realizes bound2475

private theorem bound2476 : resolveAt Program.sites 2476 = some (.inc 1 (some 2477)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2476 : AXMacro.Realizes Program.sites .incT 2476 2477 :=
  AXMacro.inc_realizes bound2476

private theorem bound2477_u : UnpairPartial.Bound Program.sites 2477 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2477_p : AXPair.Bound Program.sites 2457 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2477_t : AXTimes4.Bound Program.sites 2498 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2477 : AXMacro.Realizes Program.sites .cons 2477 2504 :=
  AXMacro.cons_realizes bound2477_u bound2477_p bound2477_t

private theorem bound2504_p : AXPushParam.Bound Program.sites 2479 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2504 : AXMacro.Realizes Program.sites .push 2504 2523 :=
  AXMacro.push_realizes bound2504_p

private theorem bound2523_c : CopyToT.Bound Program.sites 5 2523 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2523 : AXMacro.Realizes Program.sites .copyH 2523 2530 :=
  AXMacro.copyH_realizes bound2523_c

private theorem bound2530_p : AXPushParam.Bound Program.sites 2505 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2530 : AXMacro.Realizes Program.sites .push 2530 2549 :=
  AXMacro.push_realizes bound2530_p

private theorem bound2549_c : CopyToT.Bound Program.sites 4 2549 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2549 : AXMacro.Realizes Program.sites .copyD 2549 2556 :=
  AXMacro.copyD_realizes bound2549_c

private theorem bound2556_u : UnpairPartial.Bound Program.sites 2556 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2556_p : AXPair.Bound Program.sites 2536 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2556_t : AXTimes4.Bound Program.sites 2577 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2556 : AXMacro.Realizes Program.sites .cons 2556 2583 :=
  AXMacro.cons_realizes bound2556_u bound2556_p bound2556_t

private theorem bound2583 : resolveAt Program.sites 2583 = some (.inc 1 (some 2584)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2583 : AXMacro.Realizes Program.sites .incT 2583 2584 :=
  AXMacro.inc_realizes bound2583

end PA196.Source.AXBindings
