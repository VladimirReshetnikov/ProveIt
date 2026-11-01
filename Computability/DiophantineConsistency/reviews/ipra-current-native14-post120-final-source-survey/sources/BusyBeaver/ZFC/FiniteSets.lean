import BusyBeaver.ZFC.FiniteSetsCore
import BusyBeaver.ZFC.SingletonInfinity

namespace SetTheory.BusyBeaver.ZFC.FiniteSets
open Form
universe u
variable {V : Type u} {mem : V → V → Prop}

theorem quotientBase (rawMem : V → V → Prop) (witness : V)
    (h : ProfileModel.ModelsCPGIC rawMem) :
    Base (QuotientModel.quotientMember rawMem witness h) where
  toBase := SingletonInfinity.quotientBase rawMem witness h
  union := QuotientBasic.quotient_union rawMem witness h

end SetTheory.BusyBeaver.ZFC.FiniteSets
