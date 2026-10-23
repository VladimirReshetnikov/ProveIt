import BusyBeaver.ZFC.L2Control222
import BusyBeaver.ZFC.L2Macros219

/-! Control contracts of `dag219`, transferred from `dag222` through
the raw equality contracts of `Dag219Bisim`. -/
namespace SetTheory.BusyBeaver.ZFC.L2Q
open RMDag Dag219 Code254
attribute [local irreducible] Code254.P
export L2K (dist)

abbrev ifeq_eq (st : AS) (h : st.s1 = st.p2) := trCore (n := 123) rfl (L2K.ifeq_eq st h)
abbrev ifeq_ne (st : AS) (h : st.s1 ≠ st.p2) := trCore (n := 123) rfl (L2K.ifeq_ne st h)
abbrev ifeq_par1 (st : AS) (h2 : st.s2 = 0) := trCore (n := 130) rfl (L2K.ifeq_par1 st h2)
abbrev ifeq_clear (st : AS) := trCore (n := 131) rfl (L2K.ifeq_clear st)
abbrev loop136 (k : Nat) (st : AS) (h : st.s1 = k) :=
  trCore (n := 136) rfl (L2K.loop136 k st h)
abbrev fetch_pos (st : AS) (v : Nat) (hv : st.pl = v + 1) :=
  trCore (n := 133) rfl (L2K.fetch_pos st v hv)
abbrev fetch_zero (st : AS) (hpl : st.pl = 0) (h1 : st.s1 = 0) :=
  trCore (n := 133) rfl (L2K.fetch_zero st hpl h1)
abbrev mp_branch (st : AS) (hc : Clean st) := trCore (n := 150) rfl (L2K.mp_branch st hc)
abbrev nip_branch (st : AS) (hc : Clean st) (hh : st.p2 ≠ 1) :=
  trCore (n := 152) rfl (L2K.nip_branch st hc hh)
abbrev nip_halt (st : AS) (hc : Clean st) (hh : st.p2 = 1) :
    ∃ R', Run dag219 (.node 152) (enc st) .halt R' :=
  let ⟨R', h⟩ := L2K.nip_halt st hc hh
  ⟨R', trCore (n := 152) rfl h⟩

end SetTheory.BusyBeaver.ZFC.L2Q
