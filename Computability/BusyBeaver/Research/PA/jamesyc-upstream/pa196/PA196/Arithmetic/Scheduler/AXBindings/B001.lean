module
public import PA196.Arithmetic.Scheduler.AXBindings.B000
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound197_u : UnpairPartial.Bound Program.sites 197 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound197_p : AXPair.Bound Program.sites 177 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound197_t : AXTimes4.Bound Program.sites 218 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block197 : AXTyped.Bound .cons 197 224 :=
  .cons 177 (by decide) bound197_u bound197_p bound197_t

private theorem bound224_r : PA196.Source.Readers.Bound Program.sites (AXMacro.readerD 224) := by
  unfold PA196.Source.Readers.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block224 : AXTyped.Bound .readD 224 238 :=
  .readD 224 (by decide) bound224_r

private theorem bound238_p : AXPushParam.Bound Program.sites 213 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block238 : AXTyped.Bound .push 238 257 :=
  .push 213 (by decide) bound238_p

private theorem bound257_c : CopyToT.Bound Program.sites 4 257 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block257 : AXTyped.Bound .copyD 257 264 :=
  .copyD 257 (by decide) bound257_c

private theorem bound264_u : UnpairPartial.Bound Program.sites 264 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound264_p : AXPair.Bound Program.sites 244 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound264_t : AXTimes4.Bound Program.sites 285 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block264 : AXTyped.Bound .cons 264 291 :=
  .cons 244 (by decide) bound264_u bound264_p bound264_t

private theorem bound291_p : AXPushParam.Bound Program.sites 266 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block291 : AXTyped.Bound .push 291 310 :=
  .push 266 (by decide) bound291_p

private theorem bound310_c : CopyToT.Bound Program.sites 4 310 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block310 : AXTyped.Bound .copyD 310 317 :=
  .copyD 310 (by decide) bound310_c

private theorem bound317_p : AXPushParam.Bound Program.sites 292 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block317 : AXTyped.Bound .push 317 336 :=
  .push 292 (by decide) bound317_p

private theorem bound336_c : CopyToT.Bound Program.sites 5 336 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block336 : AXTyped.Bound .copyH 336 343 :=
  .copyH 336 (by decide) bound336_c

private theorem bound343_u : UnpairPartial.Bound Program.sites 343 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound343_p : AXPair.Bound Program.sites 323 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound343_t : AXTimes4.Bound Program.sites 364 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block343 : AXTyped.Bound .cons 343 370 :=
  .cons 323 (by decide) bound343_u bound343_p bound343_t

private theorem bound370_p : AXPushParam.Bound Program.sites 345 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block370 : AXTyped.Bound .push 370 389 :=
  .push 345 (by decide) bound370_p

private theorem bound389_c : CopyToT.Bound Program.sites 3 389 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block389 : AXTyped.Bound .copyA 389 396 :=
  .copyA 389 (by decide) bound389_c

end PA196.Arithmetic.Scheduler.AXBindings
