import BusyBeaver.ZFC.L2Macros254
import BusyBeaver.ZFC.L2Lib222

/-! Stack and formula contracts of `dag222`, transferred from the native 254
library through the closed node set of `L2Lib222`. -/
namespace SetTheory.BusyBeaver.ZFC.L2K
open RMDag Dag222 Code254
attribute [local irreducible] Code254.P
export L2 (Clean times4 cons_clean ofNat_P)

theorem seqAS {n : Nat} {a b : Edge} (hn : dag222.nodes n = (a, b)) {s0 s1 s2 : AS}
    (ha : Run dag222 a (enc s0) .normal (enc s1)) (hb : Run dag222 b (enc s1) .normal (enc s2)) :
    Rn (.node n) s0 s2 := seq hn ha hb

theorem rn_eq {e : Edge} {s s1 s2 : AS} (h : Rn e s s1) (he : s1 = s2) : Rn e s s2 := he ▸ h

abbrev pushwff (st : AS) (hc : Clean st) := trCore (n := 171) rfl (L2.pushwff st hc)
abbrev v1 (st : AS) (hc : Clean st) := trCore (n := 177) rfl (L2.v1 st hc)
abbrev par1 (st : AS) (hc : Clean st) := trCore (n := 166) rfl (L2.par1 st hc)
abbrev par2 (st : AS) (hc : Clean st) := trCore (n := 121) rfl (L2.par2 st hc)
abbrev par3 (st : AS) (hc : Clean st) := trCore (n := 168) rfl (L2.par3 st hc)
abbrev add2 (st : AS) := trCore (n := 159) rfl (L2.add2 st)
abbrev add3 (st : AS) := trCore (n := 157) rfl (L2.add3 st)
abbrev add4 (st : AS) := trCore (n := 156) rfl (L2.add4 st)
abbrev loop117 (st : AS) := trCore (n := 117) rfl (L2.loop117 st)
abbrev pop110 (st : AS) (hc : Clean st) := trCore (n := 160) rfl (L2.pop110 st hc)
abbrev cons (st : AS) (hc : Clean st) := trCore (n := 119) rfl (L2.cons st hc)
abbrev wel_m (st : AS) (hc : Clean st) := trCore (n := 181) rfl (L2.wel_m st hc)
abbrev wal_m (st : AS) (hc : Clean st) := trCore (n := 180) rfl (L2.wal_m st hc)
abbrev weq_m (st : AS) (hc : Clean st) := trCore (n := 182) rfl (L2.weq_m st hc)
abbrev wn_m (st : AS) (hc : Clean st) := trCore (n := 218) rfl (L2.wn_m st hc)
abbrev wa_m (st : AS) (hc : Clean st) := trCore (n := 178) rfl (L2.wa_m st hc)
abbrev wex_m (st : AS) (hc : Clean st) := trCore (n := 183) rfl (L2.wex_m st hc)
abbrev read108 (st : AS) (hc : Clean st) := trCore (n := 158) rfl (L2.read108 st hc)
abbrev read_ac (st : AS) (hc : Clean st) := trCore (n := 174) rfl (L2.read_ac st hc)
abbrev read_p1 (st : AS) (hc : Clean st) := trCore (n := 175) rfl (L2.read_p1 st hc)
abbrev read_p2 (st : AS) (hc : Clean st) := trCore (n := 176) rfl (L2.read_p2 st hc)
abbrev pop_p2 (st : AS) (hc : Clean st) := trCore (n := 170) rfl (L2.pop_p2 st hc)

end SetTheory.BusyBeaver.ZFC.L2K
