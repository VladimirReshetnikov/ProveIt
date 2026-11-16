module
public import PA196.Arithmetic.Scheduler.AXBindings.B013
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound2310_u : UnpairPartial.Bound Program.sites 2310 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2310_p : AXPair.Bound Program.sites 2290 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2310_t : AXTimes4.Bound Program.sites 2331 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2310 : AXTyped.Bound .cons 2310 2337 :=
  .cons 2290 (by decide) bound2310_u bound2310_p bound2310_t

private theorem bound2337 : resolveAt Program.sites 2337 = some (.inc 1 (some 2338)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2337 : AXTyped.Bound .incT 2337 2338 :=
  .incT 2337 (by decide) bound2337

private theorem bound2338 : resolveAt Program.sites 2338 = some (.inc 1 (some 2339)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2338 : AXTyped.Bound .incT 2338 2339 :=
  .incT 2338 (by decide) bound2338

private theorem bound2339 : resolveAt Program.sites 2339 = some (.inc 1 (some 2340)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2339 : AXTyped.Bound .incT 2339 2340 :=
  .incT 2339 (by decide) bound2339

private theorem bound2340_p : AXPushParam.Bound Program.sites 2315 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2340 : AXTyped.Bound .push 2340 2359 :=
  .push 2315 (by decide) bound2340_p

private theorem bound2359_c : CopyToT.Bound Program.sites 5 2359 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2359 : AXTyped.Bound .copyH 2359 2366 :=
  .copyH 2359 (by decide) bound2359_c

private theorem bound2366_p : AXPushParam.Bound Program.sites 2341 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2366 : AXTyped.Bound .push 2366 2385 :=
  .push 2341 (by decide) bound2366_p

private theorem bound2385_c : CopyToT.Bound Program.sites 4 2385 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2385 : AXTyped.Bound .copyD 2385 2392 :=
  .copyD 2385 (by decide) bound2385_c

private theorem bound2392_u : UnpairPartial.Bound Program.sites 2392 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2392_p : AXPair.Bound Program.sites 2372 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2392_t : AXTimes4.Bound Program.sites 2413 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2392 : AXTyped.Bound .cons 2392 2419 :=
  .cons 2372 (by decide) bound2392_u bound2392_p bound2392_t

private theorem bound2419 : resolveAt Program.sites 2419 = some (.inc 1 (some 2420)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2419 : AXTyped.Bound .incT 2419 2420 :=
  .incT 2419 (by decide) bound2419

private theorem bound2420 : resolveAt Program.sites 2420 = some (.inc 1 (some 2421)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2420 : AXTyped.Bound .incT 2420 2421 :=
  .incT 2420 (by decide) bound2420

private theorem bound2421 : resolveAt Program.sites 2421 = some (.inc 1 (some 2422)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2421 : AXTyped.Bound .incT 2421 2422 :=
  .incT 2421 (by decide) bound2421

end PA196.Arithmetic.Scheduler.AXBindings
