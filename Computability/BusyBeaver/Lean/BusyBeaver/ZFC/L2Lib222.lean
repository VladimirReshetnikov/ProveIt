import BusyBeaver.ZFC.L2Lib254
import BusyBeaver.ZFC.Dag222
import BusyBeaver.ZFC.RMTransfer

/-! Subroutine contracts of `dag222`. The state and arithmetic facts are shared
with the native 254 library. Runs from unchanged, closed nodes transfer through
`RMTransfer`; the rotated next-candidate loop is handled in `L2Control222`. -/
namespace SetTheory.BusyBeaver.ZFC.L2K

open RMDag Dag222 Code254 RMTransfer
attribute [local irreducible] Code254.P

export L2 (AS enc upd_np upd_tw upd_ws upd_ac upd_p1 upd_p2 upd_s1 upd_s2 upd_pl
  P_zero_zero P_step walkStep walkStep_ofNat updAS upd_enc_AS enc_updAS_self
  loopAS P_walkStep walk_pl walk_ws)

abbrev Rn (e : Edge) (st st' : AS) : Prop := Run dag222 e (enc st) .normal (enc st')

/-- Remove precisely the ancestors of the changed nodes 136 and 149. -/
def sharedNodes (n : Nat) : Bool :=
  n < 219 && !([0,133,135,136,139,140,141,142,143,144,145,146,147,148,149].contains n)

theorem sharedClosed : Closed Dag254.dag254 dag222 sharedNodes :=
  closed_of_bounded (N := 219)
    (fun n hn => by simp only [sharedNodes, Bool.and_eq_true, decide_eq_true_eq] at hn; exact hn.1)
    (by decide +kernel)

/-- The only program resource used by shared contracts. -/
theorem trCore {n : Nat} (hn : sharedNodes n = true) {R : Regs} {x : Exit} {R' : Regs}
    (h : Run Dag254.dag254 (.node n) R x R') : Run dag222 (.node n) R x R' :=
  node_transfer sharedClosed hn h

abbrev loop201 (st : AS) := trCore (n := 201) rfl (L2.loop201 st)
abbrev loop203 (st : AS) := trCore (n := 203) rfl (L2.loop203 st)
abbrev loop205 (st : AS) := trCore (n := 205) rfl (L2.loop205 st)
abbrev loop207 (st : AS) := trCore (n := 207) rfl (L2.loop207 st)
abbrev loop208 (st : AS) := trCore (n := 208) rfl (L2.loop208 st)
abbrev loop209 (st : AS) := trCore (n := 209) rfl (L2.loop209 st)
abbrev loop211 (st : AS) := trCore (n := 211) rfl (L2.loop211 st)
abbrev loop212 (st : AS) := trCore (n := 212) rfl (L2.loop212 st)
abbrev loop197 (st : AS) := trCore (n := 197) rfl (L2.loop197 st)
abbrev loop216 (st : AS) := trCore (n := 216) rfl (L2.loop216 st)
abbrev loop217 (st : AS) := trCore (n := 217) rfl (L2.loop217 st)
abbrev loop192 (st : AS) := trCore (n := 192) rfl (L2.loop192 st)
abbrev loop193 (st : AS) := trCore (n := 193) rfl (L2.loop193 st)
abbrev loop194 (st : AS) := trCore (n := 194) rfl (L2.loop194 st)
abbrev loop198 (st : AS) := trCore (n := 198) rfl (L2.loop198 st)
abbrev loop200 (st : AS) := trCore (n := 200) rfl (L2.loop200 st)
abbrev loop215 (st : AS) := trCore (n := 215) rfl (L2.loop215 st)
abbrev loop199 (st : AS) := trCore (n := 199) rfl (L2.loop199 st)
abbrev loop214 (st : AS) := trCore (n := 214) rfl (L2.loop214 st)
abbrev pair162 (n : Nat) (st : AS) (h : st.s1 + st.tw = n) :=
  trCore (n := 162) rfl (L2.pair162 n st h)
abbrev body154 (st : AS) := trCore (n := 154) rfl (L2.body154 st)

abbrev loop115 (st : AS) := trCore (n := 115) rfl (L2.loop115 st)
abbrev loop116 (st : AS) := trCore (n := 116) rfl (L2.loop116 st)

end SetTheory.BusyBeaver.ZFC.L2K
