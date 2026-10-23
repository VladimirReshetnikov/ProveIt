import BusyBeaver.ZFC.L2Lib222
import BusyBeaver.ZFC.Dag219Bisim

/-! Subroutine contracts of `dag219`. The state and arithmetic facts are shared
with `dag222`; runs below node 461 transfer through the equivalent equality test. -/
namespace SetTheory.BusyBeaver.ZFC.L2Q

open RMDag Dag219 Code254
attribute [local irreducible] Code254.P

export L2K (AS enc upd_np upd_tw upd_ws upd_ac upd_p1 upd_p2 upd_s1 upd_s2 upd_pl
  P_zero_zero P_step walkStep walkStep_ofNat updAS upd_enc_AS enc_updAS_self
  loopAS P_walkStep walk_pl walk_ws)

abbrev Rn (e : Edge) (st st' : AS) : Prop := Run dag219 e (enc st) .normal (enc st')

/-- The program resource used by all shared contracts. -/
theorem trCore {n : Nat} (hn : Dag219.inside 461 (.node n) = true)
    {R : Regs} {x : Exit} {R' : Regs}
    (h : Run Dag222.dag222 (.node n) R x R') : Run dag219 (.node n) R x R' :=
  Dag219.run_transfer Dag219.agree Dag219.inside222
    (RMTransfer.contract _ _ Dag219.eq222 Dag219.eq219) h hn

abbrev loop201 (st : AS) := trCore (n := 201) rfl (L2K.loop201 st)
abbrev loop203 (st : AS) := trCore (n := 203) rfl (L2K.loop203 st)
abbrev loop205 (st : AS) := trCore (n := 205) rfl (L2K.loop205 st)
abbrev loop207 (st : AS) := trCore (n := 207) rfl (L2K.loop207 st)
abbrev loop208 (st : AS) := trCore (n := 208) rfl (L2K.loop208 st)
abbrev loop209 (st : AS) := trCore (n := 209) rfl (L2K.loop209 st)
abbrev loop211 (st : AS) := trCore (n := 211) rfl (L2K.loop211 st)
abbrev loop212 (st : AS) := trCore (n := 212) rfl (L2K.loop212 st)
abbrev loop197 (st : AS) := trCore (n := 197) rfl (L2K.loop197 st)
abbrev loop216 (st : AS) := trCore (n := 216) rfl (L2K.loop216 st)
abbrev loop217 (st : AS) := trCore (n := 217) rfl (L2K.loop217 st)
abbrev loop192 (st : AS) := trCore (n := 192) rfl (L2K.loop192 st)
abbrev loop193 (st : AS) := trCore (n := 193) rfl (L2K.loop193 st)
abbrev loop194 (st : AS) := trCore (n := 194) rfl (L2K.loop194 st)
abbrev loop198 (st : AS) := trCore (n := 198) rfl (L2K.loop198 st)
abbrev loop200 (st : AS) := trCore (n := 200) rfl (L2K.loop200 st)
abbrev loop215 (st : AS) := trCore (n := 215) rfl (L2K.loop215 st)
abbrev loop199 (st : AS) := trCore (n := 199) rfl (L2K.loop199 st)
abbrev loop214 (st : AS) := trCore (n := 214) rfl (L2K.loop214 st)
abbrev pair162 (n : Nat) (st : AS) (h : st.s1 + st.tw = n) :=
  trCore (n := 162) rfl (L2K.pair162 n st h)
abbrev body154 (st : AS) := trCore (n := 154) rfl (L2K.body154 st)

abbrev loop115 (st : AS) := trCore (n := 115) rfl (L2K.loop115 st)
abbrev loop116 (st : AS) := trCore (n := 116) rfl (L2K.loop116 st)

end SetTheory.BusyBeaver.ZFC.L2Q
