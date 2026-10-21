import BusyBeaver.ZFC.KSource215Normalized

/-! Drop-in facade: the public K215 source theorem retains its exact statement. -/
namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath

theorem p215_halts_iff (R : Registers) :
    Halts p215 ⟨[], R⟩ ↔ Halts pathDagPerm ⟨[], R⟩ :=
  KSource215Normalized.p215_halts_iff R

#print axioms p215_halts_iff

end SetTheory.BusyBeaver.ZFC.KSource215
