module
public import PA196.Source.AXBindings.B010
public import PA196.Program
public import PA196.Source.Readers
public import M6.Source.AXMacroPlan
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Source.AXBindings
open M6.Source
private theorem bound1832_u : UnpairPartial.Bound Program.sites 1832 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1832_p : AXPair.Bound Program.sites 1812 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1832_t : AXTimes4.Bound Program.sites 1853 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1832 : AXMacro.Realizes Program.sites .cons 1832 1859 :=
  AXMacro.cons_realizes bound1832_u bound1832_p bound1832_t

private theorem bound1859 : resolveAt Program.sites 1859 = some (.inc 1 (some 1860)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1859 : AXMacro.Realizes Program.sites .incT 1859 1860 :=
  AXMacro.inc_realizes bound1859

private theorem bound1860 : resolveAt Program.sites 1860 = some (.inc 1 (some 1861)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1860 : AXMacro.Realizes Program.sites .incT 1860 1861 :=
  AXMacro.inc_realizes bound1860

private theorem bound1861_p : AXPushParam.Bound Program.sites 1836 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1861 : AXMacro.Realizes Program.sites .push 1861 1880 :=
  AXMacro.push_realizes bound1861_p

private theorem bound1880 : resolveAt Program.sites 1880 = some (.inc 1 (some 1881)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1880 : AXMacro.Realizes Program.sites .incT 1880 1881 :=
  AXMacro.inc_realizes bound1880

private theorem bound1881_u : UnpairPartial.Bound Program.sites 1881 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1881_p : AXPair.Bound Program.sites 1861 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1881_t : AXTimes4.Bound Program.sites 1902 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1881 : AXMacro.Realizes Program.sites .cons 1881 1908 :=
  AXMacro.cons_realizes bound1881_u bound1881_p bound1881_t

private theorem bound1908_p : AXPushParam.Bound Program.sites 1883 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1908 : AXMacro.Realizes Program.sites .push 1908 1927 :=
  AXMacro.push_realizes bound1908_p

private theorem bound1927_c : CopyToT.Bound Program.sites 3 1927 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1927 : AXMacro.Realizes Program.sites .copyA 1927 1934 :=
  AXMacro.copyA_realizes bound1927_c

private theorem bound1934_p : AXPushParam.Bound Program.sites 1909 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1934 : AXMacro.Realizes Program.sites .push 1934 1953 :=
  AXMacro.push_realizes bound1934_p

private theorem bound1953_c : CopyToT.Bound Program.sites 4 1953 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1953 : AXMacro.Realizes Program.sites .copyD 1953 1960 :=
  AXMacro.copyD_realizes bound1953_c

private theorem bound1960_u : UnpairPartial.Bound Program.sites 1960 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1960_p : AXPair.Bound Program.sites 1940 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound1960_t : AXTimes4.Bound Program.sites 1981 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block1960 : AXMacro.Realizes Program.sites .cons 1960 1987 :=
  AXMacro.cons_realizes bound1960_u bound1960_p bound1960_t

private theorem bound1987 : resolveAt Program.sites 1987 = some (.inc 1 (some 1988)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block1987 : AXMacro.Realizes Program.sites .incT 1987 1988 :=
  AXMacro.inc_realizes bound1987

end PA196.Source.AXBindings
