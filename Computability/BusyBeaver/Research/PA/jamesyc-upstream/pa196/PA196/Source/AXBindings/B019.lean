module
public import PA196.Source.AXBindings.B018
public import PA196.Program
public import PA196.Source.Readers
public import M6.Source.AXMacroPlan
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Source.AXBindings
open M6.Source
private theorem bound3092_u : UnpairPartial.Bound Program.sites 3092 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3092_p : AXPair.Bound Program.sites 3072 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3092_t : AXTimes4.Bound Program.sites 3113 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3092 : AXMacro.Realizes Program.sites .cons 3092 3119 :=
  AXMacro.cons_realizes bound3092_u bound3092_p bound3092_t

private theorem bound3119_p : AXPushParam.Bound Program.sites 3094 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3119 : AXMacro.Realizes Program.sites .push 3119 3138 :=
  AXMacro.push_realizes bound3119_p

private theorem bound3138 : resolveAt Program.sites 3138 = some (.inc 1 (some 3139)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block3138 : AXMacro.Realizes Program.sites .incT 3138 3139 :=
  AXMacro.inc_realizes bound3138

private theorem bound3139_u : UnpairPartial.Bound Program.sites 3139 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3139_p : AXPair.Bound Program.sites 3119 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3139_t : AXTimes4.Bound Program.sites 3160 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3139 : AXMacro.Realizes Program.sites .cons 3139 3166 :=
  AXMacro.cons_realizes bound3139_u bound3139_p bound3139_t

private theorem bound3166_u : UnpairPartial.Bound Program.sites 3166 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3166_p : AXPair.Bound Program.sites 3146 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3166_t : AXTimes4.Bound Program.sites 3187 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3166 : AXMacro.Realizes Program.sites .cons 3166 3193 :=
  AXMacro.cons_realizes bound3166_u bound3166_p bound3166_t

private theorem bound3193_p : AXPushParam.Bound Program.sites 3168 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3193 : AXMacro.Realizes Program.sites .push 3193 3212 :=
  AXMacro.push_realizes bound3193_p

private theorem bound3212 : resolveAt Program.sites 3212 = some (.inc 1 (some 3213)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block3212 : AXMacro.Realizes Program.sites .incT 3212 3213 :=
  AXMacro.inc_realizes bound3212

private theorem bound3213_u : UnpairPartial.Bound Program.sites 3213 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3213_p : AXPair.Bound Program.sites 3193 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3213_t : AXTimes4.Bound Program.sites 3234 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3213 : AXMacro.Realizes Program.sites .cons 3213 3240 :=
  AXMacro.cons_realizes bound3213_u bound3213_p bound3213_t

private theorem bound3240_p : AXPushParam.Bound Program.sites 3215 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3240 : AXMacro.Realizes Program.sites .push 3240 3259 :=
  AXMacro.push_realizes bound3240_p

private theorem bound3259_c : CopyToT.Bound Program.sites 4 3259 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3259 : AXMacro.Realizes Program.sites .copyD 3259 3266 :=
  AXMacro.copyD_realizes bound3259_c

private theorem bound3266_u : UnpairPartial.Bound Program.sites 3266 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3266_p : AXPair.Bound Program.sites 3246 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound3266_t : AXTimes4.Bound Program.sites 3287 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block3266 : AXMacro.Realizes Program.sites .cons 3266 3293 :=
  AXMacro.cons_realizes bound3266_u bound3266_p bound3266_t

private theorem bound3293 : resolveAt Program.sites 3293 = some (.inc 1 (some 3294)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block3293 : AXMacro.Realizes Program.sites .incT 3293 3294 :=
  AXMacro.inc_realizes bound3293

end PA196.Source.AXBindings
