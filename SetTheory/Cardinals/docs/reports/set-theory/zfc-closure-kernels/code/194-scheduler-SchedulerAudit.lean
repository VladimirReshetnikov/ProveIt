import BusyBeaver.ZFC.EnumPerm
import BusyBeaver.ZFC.Enum222
import BusyBeaver.ZFC.EnumDom
import BusyBeaver.ZFC.Enum254

namespace SetTheory.BusyBeaver.ZFC.SchedulerAudit
theorem enumPerm_old {s : EnumPerm.St} (hp : s.pl = 0) (hi : EnumPerm.Inv (EnumPerm.toW s)) :
    EnumPerm.HaltsFrom s ↔ KCode222.C222 Code254.F := EnumPerm.halts_iff hp hi

theorem enumPerm_any {s : EnumPerm.St} (hi : EnumPerm.Inv (EnumPerm.toW s)) :
    EnumPerm.HaltsFrom s ↔ KCode222.C222 Code254.F := EnumPerm.halts_iff_any hi

theorem enumPerm_active {s : EnumPerm.St} (h : KCode222.C222 Code254.F) :
    EnumPerm.HaltsFrom s := EnumPerm.complete_any h

theorem Enum254_old : Enum254.Halts ↔ Code254.C254 Code254.F := Enum254.enum_halts_iff

theorem Enum222_old : Enum222.Halts ↔ KCode222.C222 Code254.F := Enum222.enum_halts_iff

theorem EnumDom_old : EnumDom.Halts ↔ KCode222.C222 Code254.F := EnumDom.enum_halts_iff

theorem Enum254_run_add : ∀ (n m : Nat) (s t : Enum254.St),
    Enum254.run n s = some t → Enum254.run (n + m) s = Enum254.run m t := Enum254.run_add

theorem Enum222_run_add : ∀ (n m : Nat) (s t : Enum222.St),
    Enum222.run n s = some t → Enum222.run (n + m) s = Enum222.run m t := Enum222.run_add

theorem EnumDom_run_add : ∀ (n m : Nat) (s t : EnumDom.St),
    EnumDom.run n s = some t → EnumDom.run (n + m) s = EnumDom.run m t := EnumDom.run_add

theorem EnumPerm_run_add : ∀ (n m : Nat) (s t : EnumPerm.St),
    EnumPerm.run n s = some t → EnumPerm.run (n + m) s = EnumPerm.run m t := EnumPerm.run_add

#print axioms enumPerm_old
#print axioms enumPerm_any
#print axioms enumPerm_active
#print axioms Enum254_old
#print axioms Enum222_old
#print axioms EnumDom_old
#print axioms CofinalScheduler.Dynamics.reach_or_halt
#print axioms CofinalScheduler.Dynamics.complete_at
#print axioms CofinalScheduler.Dynamics.run_invariant
end SetTheory.BusyBeaver.ZFC.SchedulerAudit
