import BusyBeaver.ZFC.KSource215WfTables

/-! Nodes 32–63 of the 487-node well-formedness check. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SetTheory.BusyBeaver.ZFC.KSource215WfChunks

theorem wfChunk01 : (List.range' 32 32).all
    (RMEquiv.nodeOkb DagPerm.dagPerm 487
      (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0)) = true := by
  decide +kernel

end SetTheory.BusyBeaver.ZFC.KSource215WfChunks
#print axioms SetTheory.BusyBeaver.ZFC.KSource215WfChunks.wfChunk01
