module
public import PA196.Arithmetic.Scheduler.AXBindings.B003
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Arithmetic.Scheduler.AXBindings
open M6.Source
private theorem bound752_c : CopyToT.Bound Program.sites 5 752 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block752 : AXTyped.Bound .copyH 752 759 :=
  .copyH 752 (by decide) bound752_c

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
theorem block759 : AXTyped.Bound .cons 759 786 :=
  .cons 739 (by decide) bound759_u bound759_p bound759_t

private theorem bound786_p : AXPushParam.Bound Program.sites 761 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block786 : AXTyped.Bound .push 786 805 :=
  .push 761 (by decide) bound786_p

private theorem bound805_c : CopyToT.Bound Program.sites 5 805 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block805 : AXTyped.Bound .copyH 805 812 :=
  .copyH 805 (by decide) bound805_c

private theorem bound812_p : AXPushParam.Bound Program.sites 787 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block812 : AXTyped.Bound .push 812 831 :=
  .push 787 (by decide) bound812_p

private theorem bound831_c : CopyToT.Bound Program.sites 3 831 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block831 : AXTyped.Bound .copyA 831 838 :=
  .copyA 831 (by decide) bound831_c

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
theorem block838 : AXTyped.Bound .cons 838 865 :=
  .cons 818 (by decide) bound838_u bound838_p bound838_t

private theorem bound865 : resolveAt Program.sites 865 = some (.inc 1 (some 866)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block865 : AXTyped.Bound .incT 865 866 :=
  .incT 865 (by decide) bound865

private theorem bound866 : resolveAt Program.sites 866 = some (.inc 1 (some 867)) := by
  rw [Program.resolve_tree]
  decide +kernel
theorem block866 : AXTyped.Bound .incT 866 867 :=
  .incT 866 (by decide) bound866

private theorem bound867_p : AXPushParam.Bound Program.sites 842 := by
  unfold AXPushParam.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block867 : AXTyped.Bound .push 867 886 :=
  .push 842 (by decide) bound867_p

private theorem bound886_c : CopyToT.Bound Program.sites 4 886 := by
  unfold CopyToT.Bound
  simp only [Program.resolve_tree]
  decide +kernel
theorem block886 : AXTyped.Bound .copyD 886 893 :=
  .copyD 886 (by decide) bound886_c

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
theorem block893 : AXTyped.Bound .cons 893 920 :=
  .cons 873 (by decide) bound893_u bound893_p bound893_t

end PA196.Arithmetic.Scheduler.AXBindings
