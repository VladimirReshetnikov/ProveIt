module
public import PA196.Source.AXBindings.B011
public import PA196.Program
public import PA196.Source.Readers
public import M6.Source.AXMacroPlan
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Source.AXBindings
open M6.Source
private theorem bound1988 : resolveAt Program.sites 1988 = some (.inc 1 (some 1989)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1988 : AXMacro.Realizes Program.sites .incT 1988 1989 :=
  AXMacro.inc_realizes bound1988

private theorem bound1989_p : AXPushParam.Bound Program.sites 1964 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1989 : AXMacro.Realizes Program.sites .push 1989 2008 :=
  AXMacro.push_realizes bound1989_p

private theorem bound2008_c : CopyToT.Bound Program.sites 3 2008 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2008 : AXMacro.Realizes Program.sites .copyA 2008 2015 :=
  AXMacro.copyA_realizes bound2008_c

private theorem bound2015_p : AXPushParam.Bound Program.sites 1990 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2015 : AXMacro.Realizes Program.sites .push 2015 2034 :=
  AXMacro.push_realizes bound2015_p

private theorem bound2034_c : CopyToT.Bound Program.sites 5 2034 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2034 : AXMacro.Realizes Program.sites .copyH 2034 2041 :=
  AXMacro.copyH_realizes bound2034_c

private theorem bound2041_u : UnpairPartial.Bound Program.sites 2041 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2041_p : AXPair.Bound Program.sites 2021 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2041_t : AXTimes4.Bound Program.sites 2062 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2041 : AXMacro.Realizes Program.sites .cons 2041 2068 :=
  AXMacro.cons_realizes bound2041_u bound2041_p bound2041_t

private theorem bound2068_p : AXPushParam.Bound Program.sites 2043 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2068 : AXMacro.Realizes Program.sites .push 2068 2087 :=
  AXMacro.push_realizes bound2068_p

private theorem bound2087_c : CopyToT.Bound Program.sites 4 2087 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2087 : AXMacro.Realizes Program.sites .copyD 2087 2094 :=
  AXMacro.copyD_realizes bound2087_c

private theorem bound2094_u : UnpairPartial.Bound Program.sites 2094 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2094_p : AXPair.Bound Program.sites 2074 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound2094_t : AXTimes4.Bound Program.sites 2115 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2094 : AXMacro.Realizes Program.sites .cons 2094 2121 :=
  AXMacro.cons_realizes bound2094_u bound2094_p bound2094_t

private theorem bound2121 : resolveAt Program.sites 2121 = some (.inc 1 (some 2122)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2121 : AXMacro.Realizes Program.sites .incT 2121 2122 :=
  AXMacro.inc_realizes bound2121

private theorem bound2122 : resolveAt Program.sites 2122 = some (.inc 1 (some 2123)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block2122 : AXMacro.Realizes Program.sites .incT 2122 2123 :=
  AXMacro.inc_realizes bound2122

private theorem bound2123_p : AXPushParam.Bound Program.sites 2098 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block2123 : AXMacro.Realizes Program.sites .push 2123 2142 :=
  AXMacro.push_realizes bound2123_p

end PA196.Source.AXBindings
