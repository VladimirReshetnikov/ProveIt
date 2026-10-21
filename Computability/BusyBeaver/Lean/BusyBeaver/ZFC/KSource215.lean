import BusyBeaver.ZFC.KSource215Data
import BusyBeaver.ZFC.KSource215FwdCheck00
import BusyBeaver.ZFC.KSource215FwdCheck01
import BusyBeaver.ZFC.KSource215FwdCheck02
import BusyBeaver.ZFC.KSource215FwdCheck03
import BusyBeaver.ZFC.KSource215FwdCheck04
import BusyBeaver.ZFC.KSource215FwdCheck05
import BusyBeaver.ZFC.KSource215FwdCheck06
import BusyBeaver.ZFC.KSource215FwdCheck07
import BusyBeaver.ZFC.KSource215FwdCheck08
import BusyBeaver.ZFC.KSource215FwdCheck09
import BusyBeaver.ZFC.KSource215FwdCheck10
import BusyBeaver.ZFC.KSource215FwdCheck11
import BusyBeaver.ZFC.KSource215FwdCheck12
import BusyBeaver.ZFC.KSource215FwdCheck13
import BusyBeaver.ZFC.KSource215FwdCheck14
import BusyBeaver.ZFC.KSource215FwdCheck15

namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath RMBisim RMOffsetBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem fwd_start : obranchOk t215 tD fwdCert [] [] 0 0 = true := by decide +kernel

theorem fwd_all : allO fwdF fwdCert = true := by
  unfold fwdCert
  simp only [allO, fwd_ok0, fwd_ok1, fwd_ok2, fwd_ok3, fwd_ok4, fwd_ok5, fwd_ok6, fwd_ok7, fwd_ok8, fwd_ok9, fwd_ok10, fwd_ok11, fwd_ok12, fwd_ok13, fwd_ok14, fwd_ok15, Bool.and_self]

theorem fwd_start' : obranchOk (ptree p215) (ptree pathDagPerm) fwdCert [] [] 0 0 = true := by
  rw [t215_eq, tD_eq]; exact fwd_start

theorem fwd_all' : allO (oentryOk (ptree p215) (ptree pathDagPerm) fwdCert) fwdCert = true := by
  rw [t215_eq, tD_eq]; exact fwd_all


/-- **The 215's source and dagPerm halt alike**, from every register file. -/
theorem p215_halts_iff (R : Registers) : Halts p215 ⟨[], R⟩ ↔ Halts pathDagPerm ⟨[], R⟩ :=
  ocheck_halts_iff fwd_start' fwd_all' R

#print axioms p215_halts_iff

end SetTheory.BusyBeaver.ZFC.KSource215
