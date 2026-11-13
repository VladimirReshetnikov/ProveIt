module
public import PA196.Arithmetic.Scheduler.AXBindings.B012
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound2142_c : CopyToT.Bound Program.sites 5 2142 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2142 : AXTyped.Bound .copyH 2142 2149 :=
  .copyH 2142 (by decide) bound2142_c

private theorem bound2149_p : AXPushParam.Bound Program.sites 2124 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2149 : AXTyped.Bound .push 2149 2168 :=
  .push 2124 (by decide) bound2149_p

private theorem bound2168_c : CopyToT.Bound Program.sites 4 2168 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2168 : AXTyped.Bound .copyD 2168 2175 :=
  .copyD 2168 (by decide) bound2168_c

private theorem bound2175_u : UnpairPartial.Bound Program.sites 2175 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2175_p : AXPair.Bound Program.sites 2155 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2175_t : AXTimes4.Bound Program.sites 2196 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2175 : AXTyped.Bound .cons 2175 2202 :=
  .cons 2155 (by decide) bound2175_u bound2175_p bound2175_t

private theorem bound2202 : resolveAt Program.sites 2202 = some (.inc 1 (some 2203)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2202 : AXTyped.Bound .incT 2202 2203 :=
  .incT 2202 (by decide) bound2202

private theorem bound2203 : resolveAt Program.sites 2203 = some (.inc 1 (some 2204)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2203 : AXTyped.Bound .incT 2203 2204 :=
  .incT 2203 (by decide) bound2203

private theorem bound2204_u : UnpairPartial.Bound Program.sites 2204 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2204_p : AXPair.Bound Program.sites 2184 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2204_t : AXTimes4.Bound Program.sites 2225 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2204 : AXTyped.Bound .cons 2204 2231 :=
  .cons 2184 (by decide) bound2204_u bound2204_p bound2204_t

private theorem bound2231_u : UnpairPartial.Bound Program.sites 2231 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2231_p : AXPair.Bound Program.sites 2211 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2231_t : AXTimes4.Bound Program.sites 2252 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2231 : AXTyped.Bound .cons 2231 2258 :=
  .cons 2211 (by decide) bound2231_u bound2231_p bound2231_t

private theorem bound2258_p : AXPushParam.Bound Program.sites 2233 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2258 : AXTyped.Bound .push 2258 2277 :=
  .push 2233 (by decide) bound2258_p

private theorem bound2277_c : CopyToT.Bound Program.sites 5 2277 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2277 : AXTyped.Bound .copyH 2277 2284 :=
  .copyH 2277 (by decide) bound2277_c

private theorem bound2284_p : AXPushParam.Bound Program.sites 2259 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2284 : AXTyped.Bound .push 2284 2303 :=
  .push 2259 (by decide) bound2284_p

private theorem bound2303_c : CopyToT.Bound Program.sites 4 2303 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2303 : AXTyped.Bound .copyD 2303 2310 :=
  .copyD 2303 (by decide) bound2303_c

end PA196.Arithmetic.Scheduler.AXBindings
