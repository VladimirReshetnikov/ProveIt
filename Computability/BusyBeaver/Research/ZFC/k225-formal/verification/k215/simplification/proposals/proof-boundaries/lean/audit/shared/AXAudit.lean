import BusyBeaver.ZFC.L2RootPerm
import BusyBeaver.ZFC.L2RootDom
import BusyBeaver.ZFC.SeedPerm

namespace AXAudit
open SetTheory.BusyBeaver.ZFC

-- Exact bindings: the common semantics never weakens the literal program check.
theorem reject_permuted_for_dom :
    AXWord.axWordCheck DagDom.dagDom 236 (AXWord.axWord true) = false := by decide +kernel

theorem reject_dom_for_permuted :
    AXWord.axWordCheck DagPerm.dagPerm 236 (AXWord.axWord false) = false := by decide +kernel

theorem reject_wrong_start :
    AXWord.axWordCheck DagPerm.dagPerm 237 (AXWord.axWord true) = false := by decide +kernel

theorem reject_truncated :
    AXWord.axWordCheck DagPerm.dagPerm 236 ((AXWord.axWord true).take 155) = false := by decide +kernel

theorem reject_wrong_atom :
    AXWord.axWordCheck DagPerm.dagPerm 236
      (AXWord.AXAtom.wn :: (AXWord.axWord true).drop 1) = false := by decide +kernel

#print axioms AXWord.cons_readp1
#print axioms AXWord.eval_permuted
#print axioms L2Perm.l236
#print axioms L2Perm.ax_eval
#print axioms L2Dom.l236
#print axioms L2Dom.ax_eval
#print axioms L2Perm.root_step
#print axioms L2Dom.root_step
#print axioms L2Perm.dagPerm_seed_iff
end AXAudit
