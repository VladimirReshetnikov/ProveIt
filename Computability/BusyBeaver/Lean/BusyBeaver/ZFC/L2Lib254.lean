import BusyBeaver.ZFC.Dag254
import BusyBeaver.ZFC.Enum254

/-!
Subroutine semantics of the 219-node register program (L2, part 1).

The register file is related to a nine-field record. Every loop node of the
program is one of three shapes — transfer `src → dst`, copy `src → d₁, d₂`,
or clear — and the program's subroutines are compositions of these:
`pushwff` (`ws := P(tw, ws)`), the parameter pushes, `pair`
(`out += P(in₁, in₂)`), the unpair walk, `read`, `pop`, the formula
constructors and the destructive equality test. The pairing stays opaque.
-/

namespace SetTheory.BusyBeaver.ZFC.L2

open RMDag Dag254 Code254

attribute [local irreducible] Code254.P

/-- The nine registers, in declaration order. -/
structure AS where
  np : Nat
  tw : Nat
  ws : Nat
  ac : Nat
  p1 : Nat
  p2 : Nat
  s1 : Nat
  s2 : Nat
  pl : Nat

def enc (st : AS) : Regs
  | 0 => st.np
  | 1 => st.tw
  | 2 => st.ws
  | 3 => st.ac
  | 4 => st.p1
  | 5 => st.p2
  | 6 => st.s1
  | 7 => st.s2
  | 8 => st.pl
  | _ => 0

abbrev Rn (e : Edge) (st st' : AS) : Prop := Run dag254 e (enc st) .normal (enc st')

@[simp] theorem upd_np (st : AS) (v : Nat) : upd (enc st) 0 v = enc { st with np := v } := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

@[simp] theorem upd_tw (st : AS) (v : Nat) : upd (enc st) 1 v = enc { st with tw := v } := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

@[simp] theorem upd_ws (st : AS) (v : Nat) : upd (enc st) 2 v = enc { st with ws := v } := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

@[simp] theorem upd_ac (st : AS) (v : Nat) : upd (enc st) 3 v = enc { st with ac := v } := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

@[simp] theorem upd_p1 (st : AS) (v : Nat) : upd (enc st) 4 v = enc { st with p1 := v } := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

@[simp] theorem upd_p2 (st : AS) (v : Nat) : upd (enc st) 5 v = enc { st with p2 := v } := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

@[simp] theorem upd_s1 (st : AS) (v : Nat) : upd (enc st) 6 v = enc { st with s1 := v } := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

@[simp] theorem upd_s2 (st : AS) (v : Nat) : upd (enc st) 7 v = enc { st with s2 := v } := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

@[simp] theorem upd_pl (st : AS) (v : Nat) : upd (enc st) 8 v = enc { st with pl := v } := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

/-! ## Loop instances -/

/-- `s1 → ac` -/
theorem loop201 (st : AS) : Rn (.node 201) st { st with ac := st.ac + st.s1, s1 := 0 } := by
  have := transfer (p := dag254) (n := 201) (m := 202) (src := 6) (dst := 3) rfl rfl (by decide) (enc st)
  simpa [enc] using this

/-- `s1 → np` -/
theorem loop203 (st : AS) : Rn (.node 203) st { st with np := st.np + st.s1, s1 := 0 } := by
  have := transfer (p := dag254) (n := 203) (m := 204) (src := 6) (dst := 0) rfl rfl (by decide) (enc st)
  simpa [enc] using this

/-- `s1 → p1` -/
theorem loop205 (st : AS) : Rn (.node 205) st { st with p1 := st.p1 + st.s1, s1 := 0 } := by
  have := transfer (p := dag254) (n := 205) (m := 206) (src := 6) (dst := 4) rfl rfl (by decide) (enc st)
  simpa [enc] using this

/-- `s1 → p2` -/
theorem loop207 (st : AS) : Rn (.node 207) st { st with p2 := st.p2 + st.s1, s1 := 0 } := by
  have := transfer (p := dag254) (n := 207) (m := 191) (src := 6) (dst := 5) rfl rfl (by decide) (enc st)
  simpa [enc] using this

/-- `s1 → tw` -/
theorem loop208 (st : AS) : Rn (.node 208) st { st with tw := st.tw + st.s1, s1 := 0 } := by
  have := transfer (p := dag254) (n := 208) (m := 186) (src := 6) (dst := 1) rfl rfl (by decide) (enc st)
  simpa [enc] using this

/-- `s2 → pl` -/
theorem loop209 (st : AS) : Rn (.node 209) st { st with pl := st.pl + st.s2, s2 := 0 } := by
  have := transfer (p := dag254) (n := 209) (m := 210) (src := 7) (dst := 8) rfl rfl (by decide) (enc st)
  simpa [enc] using this

/-- `s2 → s1` -/
theorem loop211 (st : AS) : Rn (.node 211) st { st with s1 := st.s1 + st.s2, s2 := 0 } := by
  have := transfer (p := dag254) (n := 211) (m := 185) (src := 7) (dst := 6) rfl rfl (by decide) (enc st)
  simpa [enc] using this

/-- `s2 → ws` -/
theorem loop212 (st : AS) : Rn (.node 212) st { st with ws := st.ws + st.s2, s2 := 0 } := by
  have := transfer (p := dag254) (n := 212) (m := 213) (src := 7) (dst := 2) rfl rfl (by decide) (enc st)
  simpa [enc] using this

/-- `p1 → p2` -/
theorem loop197 (st : AS) : Rn (.node 197) st { st with p2 := st.p2 + st.p1, p1 := 0 } := by
  have := transfer (p := dag254) (n := 197) (m := 191) (src := 4) (dst := 5) rfl rfl (by decide) (enc st)
  simpa [enc] using this

/-- `tw → s1` -/
theorem loop216 (st : AS) : Rn (.node 216) st { st with s1 := st.s1 + st.tw, tw := 0 } := by
  have := transfer (p := dag254) (n := 216) (m := 185) (src := 1) (dst := 6) rfl rfl (by decide) (enc st)
  simpa [enc] using this

/-- `ws → tw` -/
theorem loop217 (st : AS) : Rn (.node 217) st { st with tw := st.tw + st.ws, ws := 0 } := by
  have := transfer (p := dag254) (n := 217) (m := 186) (src := 2) (dst := 1) rfl rfl (by decide) (enc st)
  simpa [enc] using this

/-- `ac → s1, s2` -/
theorem loop192 (st : AS) :
    Rn (.node 192) st { st with s1 := st.s1 + st.ac, s2 := st.s2 + st.ac, ac := 0 } := by
  have := copy2 (p := dag254) (n := 192) (m := 187) (m' := 188) (src := 3) (d1 := 6) (d2 := 7)
    rfl rfl rfl (by decide) (by decide) (by decide) (enc st)
  simpa [enc] using this

/-- `ac → s1, tw` -/
theorem loop193 (st : AS) :
    Rn (.node 193) st { st with s1 := st.s1 + st.ac, tw := st.tw + st.ac, ac := 0 } := by
  have := copy2 (p := dag254) (n := 193) (m := 189) (m' := 190) (src := 3) (d1 := 6) (d2 := 1)
    rfl rfl rfl (by decide) (by decide) (by decide) (enc st)
  simpa [enc] using this

/-- `np → pl, s1` -/
theorem loop194 (st : AS) :
    Rn (.node 194) st { st with pl := st.pl + st.np, s1 := st.s1 + st.np, np := 0 } := by
  have := copy2 (p := dag254) (n := 194) (m := 195) (m' := 196) (src := 0) (d1 := 8) (d2 := 6)
    rfl rfl rfl (by decide) (by decide) (by decide) (enc st)
  simpa [enc] using this

/-- `p1 → s1, tw` -/
theorem loop198 (st : AS) :
    Rn (.node 198) st { st with s1 := st.s1 + st.p1, tw := st.tw + st.p1, p1 := 0 } := by
  have := copy2 (p := dag254) (n := 198) (m := 189) (m' := 190) (src := 4) (d1 := 6) (d2 := 1)
    rfl rfl rfl (by decide) (by decide) (by decide) (enc st)
  simpa [enc] using this

/-- `p2 → s1, tw` -/
theorem loop200 (st : AS) :
    Rn (.node 200) st { st with s1 := st.s1 + st.p2, tw := st.tw + st.p2, p2 := 0 } := by
  have := copy2 (p := dag254) (n := 200) (m := 189) (m' := 190) (src := 5) (d1 := 6) (d2 := 1)
    rfl rfl rfl (by decide) (by decide) (by decide) (enc st)
  simpa [enc] using this

/-- `tw → s1, s2` -/
theorem loop215 (st : AS) :
    Rn (.node 215) st { st with s1 := st.s1 + st.tw, s2 := st.s2 + st.tw, tw := 0 } := by
  have := copy2 (p := dag254) (n := 215) (m := 187) (m' := 188) (src := 1) (d1 := 6) (d2 := 7)
    rfl rfl rfl (by decide) (by decide) (by decide) (enc st)
  simpa [enc] using this

/-- clear `p2` -/
theorem loop199 (st : AS) : Rn (.node 199) st { st with p2 := 0 } := by
  have := clear (p := dag254) (n := 199) (r := 5) rfl (enc st)
  simpa [enc] using this

/-- clear `tw` -/
theorem loop214 (st : AS) : Rn (.node 214) st { st with tw := 0 } := by
  have := clear (p := dag254) (n := 214) (r := 1) rfl (enc st)
  simpa [enc] using this

end SetTheory.BusyBeaver.ZFC.L2
