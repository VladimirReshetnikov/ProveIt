module
public import PA196.Source.AXBindings.B003
public import PA196.Program
public import PA196.Source.Readers
public import M6.Source.AXMacroPlan
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Source.AXBindings
open M6.Source
private theorem bound752_c : CopyToT.Bound Program.sites 5 752 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block752 : AXMacro.Realizes Program.sites .copyH 752 759 :=
  AXMacro.copyH_realizes bound752_c

private theorem bound759_u : UnpairPartial.Bound Program.sites 759 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound759_p : AXPair.Bound Program.sites 739 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound759_t : AXTimes4.Bound Program.sites 780 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block759 : AXMacro.Realizes Program.sites .cons 759 786 :=
  AXMacro.cons_realizes bound759_u bound759_p bound759_t

private theorem bound786_p : AXPushParam.Bound Program.sites 761 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block786 : AXMacro.Realizes Program.sites .push 786 805 :=
  AXMacro.push_realizes bound786_p

private theorem bound805_c : CopyToT.Bound Program.sites 5 805 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block805 : AXMacro.Realizes Program.sites .copyH 805 812 :=
  AXMacro.copyH_realizes bound805_c

private theorem bound812_p : AXPushParam.Bound Program.sites 787 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block812 : AXMacro.Realizes Program.sites .push 812 831 :=
  AXMacro.push_realizes bound812_p

private theorem bound831_c : CopyToT.Bound Program.sites 3 831 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block831 : AXMacro.Realizes Program.sites .copyA 831 838 :=
  AXMacro.copyA_realizes bound831_c

private theorem bound838_u : UnpairPartial.Bound Program.sites 838 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound838_p : AXPair.Bound Program.sites 818 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound838_t : AXTimes4.Bound Program.sites 859 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block838 : AXMacro.Realizes Program.sites .cons 838 865 :=
  AXMacro.cons_realizes bound838_u bound838_p bound838_t

private theorem bound865 : resolveAt Program.sites 865 = some (.inc 1 (some 866)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block865 : AXMacro.Realizes Program.sites .incT 865 866 :=
  AXMacro.inc_realizes bound865

private theorem bound866 : resolveAt Program.sites 866 = some (.inc 1 (some 867)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block866 : AXMacro.Realizes Program.sites .incT 866 867 :=
  AXMacro.inc_realizes bound866

private theorem bound867_p : AXPushParam.Bound Program.sites 842 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block867 : AXMacro.Realizes Program.sites .push 867 886 :=
  AXMacro.push_realizes bound867_p

private theorem bound886_c : CopyToT.Bound Program.sites 4 886 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block886 : AXMacro.Realizes Program.sites .copyD 886 893 :=
  AXMacro.copyD_realizes bound886_c

private theorem bound893_u : UnpairPartial.Bound Program.sites 893 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound893_p : AXPair.Bound Program.sites 873 := by
  unfold AXPair.Bound
  simp only [Program.resolve_tree]
  decide +kernel
private theorem bound893_t : AXTimes4.Bound Program.sites 914 := by
  unfold AXTimes4.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block893 : AXMacro.Realizes Program.sites .cons 893 920 :=
  AXMacro.cons_realizes bound893_u bound893_p bound893_t

end PA196.Source.AXBindings
