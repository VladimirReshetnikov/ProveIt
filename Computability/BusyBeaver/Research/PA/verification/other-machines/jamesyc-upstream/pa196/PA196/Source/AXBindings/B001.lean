module
public import PA196.Source.AXBindings.B000
public import PA196.Program
public import PA196.Source.Readers
public import M6.Source.AXMacroPlan
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Source.AXBindings
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
theorem block197 : AXMacro.Realizes Program.sites .cons 197 224 :=
  AXMacro.cons_realizes bound197_u bound197_p bound197_t

private theorem bound224_r : Readers.Bound Program.sites (AXMacro.readerD 224) := by
  unfold Readers.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block224 : AXMacro.Realizes Program.sites .readD 224 238 :=
  Readers.readD_realizes 224 bound224_r

private theorem bound238_p : AXPushParam.Bound Program.sites 213 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block238 : AXMacro.Realizes Program.sites .push 238 257 :=
  AXMacro.push_realizes bound238_p

private theorem bound257_c : CopyToT.Bound Program.sites 4 257 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block257 : AXMacro.Realizes Program.sites .copyD 257 264 :=
  AXMacro.copyD_realizes bound257_c

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
theorem block264 : AXMacro.Realizes Program.sites .cons 264 291 :=
  AXMacro.cons_realizes bound264_u bound264_p bound264_t

private theorem bound291_p : AXPushParam.Bound Program.sites 266 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block291 : AXMacro.Realizes Program.sites .push 291 310 :=
  AXMacro.push_realizes bound291_p

private theorem bound310_c : CopyToT.Bound Program.sites 4 310 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block310 : AXMacro.Realizes Program.sites .copyD 310 317 :=
  AXMacro.copyD_realizes bound310_c

private theorem bound317_p : AXPushParam.Bound Program.sites 292 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block317 : AXMacro.Realizes Program.sites .push 317 336 :=
  AXMacro.push_realizes bound317_p

private theorem bound336_c : CopyToT.Bound Program.sites 5 336 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block336 : AXMacro.Realizes Program.sites .copyH 336 343 :=
  AXMacro.copyH_realizes bound336_c

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
theorem block343 : AXMacro.Realizes Program.sites .cons 343 370 :=
  AXMacro.cons_realizes bound343_u bound343_p bound343_t

private theorem bound370_p : AXPushParam.Bound Program.sites 345 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block370 : AXMacro.Realizes Program.sites .push 370 389 :=
  AXMacro.push_realizes bound370_p

private theorem bound389_c : CopyToT.Bound Program.sites 3 389 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block389 : AXMacro.Realizes Program.sites .copyA 389 396 :=
  AXMacro.copyA_realizes bound389_c

end PA196.Source.AXBindings
