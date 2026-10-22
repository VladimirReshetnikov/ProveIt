import BusyBeaver.ZFC.L2RootPerm
import BusyBeaver.ZFC.L2RootDom
import BusyBeaver.ZFC.SeedPerm

namespace AXAudit
open SetTheory.BusyBeaver.ZFC

theorem reject_wrong_start :
    L2Perm.axWordCheck 237 L2Perm.axWord = false := by decide +kernel

theorem reject_truncated :
    L2Perm.axWordCheck 236 (L2Perm.axWord.take 155) = false := by decide +kernel

theorem reject_wrong_atom :
    L2Perm.axWordCheck 236 (L2Perm.AXAtom.wn :: L2Perm.axWord.drop 1) = false := by decide +kernel

#print axioms L2Perm.l236
#print axioms L2Perm.ax_eval
#print axioms L2Dom.l236
#print axioms L2Dom.ax_eval
#print axioms L2Perm.root_step
#print axioms L2Dom.root_step
#print axioms L2Perm.dagPerm_seed_iff
end AXAudit
