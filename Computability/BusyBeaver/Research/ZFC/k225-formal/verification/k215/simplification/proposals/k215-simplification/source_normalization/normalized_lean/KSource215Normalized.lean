import BusyBeaver.ZFC.KSource215NormalizedCheck00
import BusyBeaver.ZFC.KSource215NormalizedCheck01
import BusyBeaver.ZFC.KSource215NormalizedCheck02
import BusyBeaver.ZFC.KSource215NormalizedCheck03
import BusyBeaver.ZFC.KSource215NormalizedCheck04
import BusyBeaver.ZFC.KSource215NormalizedCheck05
import BusyBeaver.ZFC.KSource215NormalizedCheck06
import BusyBeaver.ZFC.KSource215NormalizedCheck07
import BusyBeaver.ZFC.KSource215NormalizedCheck08
import BusyBeaver.ZFC.KSource215NormalizedCheck09
import BusyBeaver.ZFC.KSource215NormalizedCheck10
import BusyBeaver.ZFC.KSource215NormalizedCheck11
import BusyBeaver.ZFC.KSource215NormalizedCheck12
import BusyBeaver.ZFC.KSource215NormalizedCheck13
import BusyBeaver.ZFC.KSource215NormalizedCheck14
import BusyBeaver.ZFC.KSource215NormalizedCheck15

namespace SetTheory.BusyBeaver.ZFC.KSource215Normalized

open RegisterPath RMBisim RMNormalizedBisim KSource215
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem start_ok : RMNormalizedBisim.branchOk t215 tD certificate [] [] 0 = true := by decide +kernel

theorem all_ok : allC checkEntry certificate = true := by
  unfold certificate
  simp only [allC, chunk_ok0, chunk_ok1, chunk_ok2, chunk_ok3, chunk_ok4, chunk_ok5, chunk_ok6, chunk_ok7, chunk_ok8, chunk_ok9, chunk_ok10, chunk_ok11, chunk_ok12, chunk_ok13, chunk_ok14, chunk_ok15, Bool.and_self]

theorem start_ok' : RMNormalizedBisim.branchOk (ptree p215) (ptree pathDagPerm) certificate [] [] 0 = true := by
  rw [t215_eq, tD_eq]; exact start_ok

theorem all_ok' : allC (RMNormalizedBisim.entryOk (ptree p215) (ptree pathDagPerm) certificate) certificate = true := by
  rw [t215_eq, tD_eq]; exact all_ok

theorem p215_halts_iff (R : Registers) : Halts p215 ⟨[], R⟩ ↔ Halts pathDagPerm ⟨[], R⟩ :=
  RMNormalizedBisim.check_halts_iff start_ok' all_ok' R

#print axioms p215_halts_iff

end SetTheory.BusyBeaver.ZFC.KSource215Normalized
