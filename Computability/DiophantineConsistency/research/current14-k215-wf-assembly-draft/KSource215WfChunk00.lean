import BusyBeaver.ZFC.KSource215WfTables

/-! First 32 actual DAG-node checks; the other 455 nodes and assembly are separate. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SetTheory.BusyBeaver.ZFC.KSource215WfChunks

theorem wfChunk00 : (List.range' 0 32).all
    (RMEquiv.nodeOkb DagPerm.dagPerm 487
      (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0)) = true := by
  decide +kernel

end SetTheory.BusyBeaver.ZFC.KSource215WfChunks
#print axioms SetTheory.BusyBeaver.ZFC.KSource215WfChunks.wfChunk00
