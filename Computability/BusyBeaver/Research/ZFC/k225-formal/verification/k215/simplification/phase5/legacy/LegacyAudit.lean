import BusyBeaver.ZFC.L2Root222
import BusyBeaver.ZFC.L2Root219
import BusyBeaver.ZFC.L2RootDom
import BusyBeaver.ZFC.L2RootPerm
import BusyBeaver.ZFC.RMOffsetBisim

namespace SetTheory.BusyBeaver.ZFC.LegacyAudit

theorem root222 (s : Enum222.St) :
    RMDag.IterHalts Dag222.dag222 (L2K.enc (L2K.toAS s)) ↔
      ∃ n s', Enum222.run n s = some s' ∧ Enum222.enumStep s' = none :=
  L2K.iter_iff s

theorem root219 (s : Enum222.St) :
    RMDag.IterHalts Dag219.dag219 (L2Q.enc (L2Q.toAS s)) ↔
      ∃ n s', Enum222.run n s = some s' ∧ Enum222.enumStep s' = none :=
  L2Q.iter_iff s

theorem rootDom (s : EnumDom.St) :
    RMDag.IterHalts DagDom.dagDom (L2K.enc (L2Dom.toAS s)) ↔
      ∃ n s', EnumDom.run n s = some s' ∧ EnumDom.enumStep s' = none :=
  L2Dom.iter_iff s

theorem rootPerm (s : EnumPerm.St) :
    RMDag.IterHalts DagPerm.dagPerm (L2K.enc (L2Perm.toAS s)) ↔
      ∃ n s', EnumPerm.run n s = some s' ∧ EnumPerm.enumStep s' = none :=
  L2Perm.iter_iff s

theorem offset_checker {p1 p2 : RegisterPath.Program} {T : RMOffsetBisim.OTree}
    (hs : RMOffsetBisim.obranchOk (RMBisim.ptree p1) (RMBisim.ptree p2) T [] [] 0 0 = true)
    (ha : RMOffsetBisim.allO (RMOffsetBisim.oentryOk (RMBisim.ptree p1) (RMBisim.ptree p2) T) T = true)
    (R : RegisterPath.Registers) :
    RegisterPath.Halts p1 ⟨[], R⟩ ↔ RegisterPath.Halts p2 ⟨[], R⟩ :=
  RMOffsetBisim.ocheck_halts_iff hs ha R

#print axioms root222
#print axioms root219
#print axioms rootDom
#print axioms rootPerm
#print axioms offset_checker

end SetTheory.BusyBeaver.ZFC.LegacyAudit
