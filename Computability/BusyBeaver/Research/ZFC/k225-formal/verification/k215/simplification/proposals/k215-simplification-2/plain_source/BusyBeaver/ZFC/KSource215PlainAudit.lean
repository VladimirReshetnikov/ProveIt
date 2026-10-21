import BusyBeaver.ZFC.KSource215

/-! Exact public source interfaces for the all-zero-offset K215 proof.
This audit does not import KEndpoint215 or assert a fresh binary endpoint build.
-/
namespace SetTheory.BusyBeaver.ZFC.KSource215PlainAudit
open RegisterPath

theorem source_halts_iff (R : Registers) :
    Halts KSource215.p215 ⟨[], R⟩ ↔ Halts KSource215.pathDagPerm ⟨[], R⟩ :=
  KSource215.p215_halts_iff R

theorem source_halts_iff_iter (R : Registers) :
    Halts KSource215.p215 ⟨[], R⟩ ↔ RMDag.IterHalts DagPerm.dagPerm R :=
  (source_halts_iff R).trans (KSource215.path_iff_iter R)

#print axioms source_halts_iff
#print axioms source_halts_iff_iter
#print axioms KSource215.t215_eq
#print axioms KSource215.tD_eq
#print axioms KSource215.wfCheck222
#print axioms RMPlainCodec.check_halts_iff
end SetTheory.BusyBeaver.ZFC.KSource215PlainAudit
