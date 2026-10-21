import BusyBeaver.ZFC.KSource215AutoCheck00
import BusyBeaver.ZFC.KSource215AutoCheck01
import BusyBeaver.ZFC.KSource215AutoCheck02
import BusyBeaver.ZFC.KSource215AutoCheck03
import BusyBeaver.ZFC.KSource215AutoCheck04
import BusyBeaver.ZFC.KSource215AutoCheck05
import BusyBeaver.ZFC.KSource215AutoCheck06
import BusyBeaver.ZFC.KSource215AutoCheck07
import BusyBeaver.ZFC.KSource215AutoCheck08
import BusyBeaver.ZFC.KSource215AutoCheck09
import BusyBeaver.ZFC.KSource215AutoCheck10
import BusyBeaver.ZFC.KSource215AutoCheck11
import BusyBeaver.ZFC.KSource215AutoCheck12
import BusyBeaver.ZFC.KSource215AutoCheck13
import BusyBeaver.ZFC.KSource215AutoCheck14
import BusyBeaver.ZFC.KSource215AutoCheck15
namespace SetTheory.BusyBeaver.ZFC.KSource215Auto
open RegisterPath RMBisim KSource215
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem start_ok : RMNormalizedBisim.branchOk t215 tD inferredCertificate [] [] 0 = true := by decide +kernel

theorem all_ok : allC checkEntry inferredCertificate = true := by
  unfold inferredCertificate
  simp only [allC, block_ok0, block_ok1, block_ok2, block_ok3, block_ok4, block_ok5, block_ok6, block_ok7, block_ok8, block_ok9, block_ok10, block_ok11, block_ok12, block_ok13, block_ok14, block_ok15, Bool.and_self]

theorem source_halts_iff (R : Registers) :
    Halts p215 ⟨[], R⟩ ↔ Halts pathDagPerm ⟨[], R⟩ := by
  apply RMNormalizedBisim.check_halts_iff (T := inferredCertificate)
  · rw [t215_eq, tD_eq]; exact start_ok
  · rw [t215_eq, tD_eq]; exact all_ok

#print axioms source_halts_iff
end SetTheory.BusyBeaver.ZFC.KSource215Auto
