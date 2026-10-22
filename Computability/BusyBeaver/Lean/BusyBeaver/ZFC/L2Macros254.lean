import BusyBeaver.ZFC.L2Lib254

/-!
The stack and formula macros of the 219-node program (L2, part 2).

Every macro is stated on a *clean* record (`s1 = s2 = 0`) and returns a
clean record:

| node | macro | effect |
|---|---|---|
| 171 | `pushwff` | `ws := P(tw, ws)`, `tw := 0` |
| 177 | `v_1` | push, `tw := 1` |
| 166, 121, 168 | `par1`, `par2`, `par3` | push, `tw := param1 / param2 / axiomcode` |
| 119 | `cons` | `(top, rest) := unP ws`; `tw := Imp(top, tw)`, `ws := rest` |
| 181, 180, 182 | `wel`, `wal`, `weq` | `tw := Rel / All / Eq (top, tw)` |
| 218, 178, 183 | `wn`, `wa`, `wex` | negation, conjunction, existential |
| 174, 175, 176 | `read` | `(x, pl) := unP pl`; register `+= x` |
| 170 | `pop(param2)` | `(top, rest) := unP ws`; `param2 += top`, `ws := rest` |

Here `Imp(a,b) = 4·P(a,b)` and the other constructors add their tags.
-/

namespace SetTheory.BusyBeaver.ZFC.L2

open RMDag Dag254 Code254

attribute [local irreducible] Code254.P

theorem seqAS {n : Nat} {a b : Edge} (hn : dag254.nodes n = (a, b)) {s0 s1 s2 : AS}
    (ha : Run dag254 a (enc s0) .normal (enc s1)) (hb : Run dag254 b (enc s1) .normal (enc s2)) :
    Rn (.node n) s0 s2 := seq hn ha hb

theorem rn_eq {e : Edge} {s s1 s2 : AS} (h : Rn e s s1) (he : s1 = s2) : Rn e s s2 := he ▸ h

theorem inc_AS (r : Nat) (hr : r < 9) (st : AS) :
    Run dag254 (.inc r) (enc st) .normal (enc (updAS st r (enc st r + 1))) := by
  have := Run.inc (p := dag254) r (enc st)
  rwa [upd_enc_AS st r _ hr] at this

/-- A clean record. -/
def Clean (st : AS) : Prop := st.s1 = 0 ∧ st.s2 = 0

/-! ## Pushes -/

theorem pushwff (st : AS) (hc : Clean st) :
    Rn (.node 171) st { st with tw := 0, ws := P st.tw st.ws } :=
  rn_eq (seqAS (n := 171) rfl (loop216 st) (seqAS (n := 172) rfl (loop217 _)
    (seqAS (n := 173) rfl (pair162 _ _ rfl) (loop212 _)))) (by
      obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1 h2; simp)

theorem v1 (st : AS) (hc : Clean st) : Rn (.node 177) st { st with tw := 1, ws := P st.tw st.ws } :=
  rn_eq (seqAS (n := 177) rfl (pushwff st hc) (inc_AS 1 (by omega) _)) (by simp [updAS, enc])

theorem par1 (st : AS) (hc : Clean st) : Rn (.node 166) st { st with tw := st.p1, ws := P st.tw st.ws } :=
  rn_eq (seqAS (n := 166) rfl (pushwff st hc) (seqAS (n := 167) rfl (loop198 _) (loop205 _))) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1 h2; simp)

theorem par2 (st : AS) (hc : Clean st) : Rn (.node 121) st { st with tw := st.p2, ws := P st.tw st.ws } :=
  rn_eq (seqAS (n := 121) rfl (pushwff st hc) (seqAS (n := 122) rfl (loop200 _) (loop207 _))) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1 h2; simp)

theorem par3 (st : AS) (hc : Clean st) : Rn (.node 168) st { st with tw := st.ac, ws := P st.tw st.ws } :=
  rn_eq (seqAS (n := 168) rfl (pushwff st hc) (seqAS (n := 169) rfl (loop193 _) (loop201 _))) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1 h2; simp)

/-! ## Constructors -/

theorem add2 (st : AS) : Rn (.node 159) st { st with tw := st.tw + 2 } :=
  rn_eq (seqAS (n := 159) rfl (inc_AS 1 (by omega) st) (inc_AS 1 (by omega) _)) (by simp [updAS, enc])

theorem add3 (st : AS) : Rn (.node 157) st { st with tw := st.tw + 3 } :=
  rn_eq (seqAS (n := 157) rfl (add2 st) (inc_AS 1 (by omega) _)) (by simp [updAS, enc])

theorem add4 (st : AS) : Rn (.node 156) st { st with tw := st.tw + 4 } :=
  rn_eq (seqAS (n := 156) rfl (add3 st) (inc_AS 1 (by omega) _)) (by simp [updAS, enc])

theorem times4 : ∀ (k : Nat) (st : AS), st.s2 = k →
    loopAS (fun st => { st with tw := st.tw + 4 }) 7 k st = { st with tw := st.tw + 4 * k, s2 := 0 }
  | 0, st, hk => by cases st; simp only at hk; subst hk; simp [loopAS]
  | k + 1, st, hk => by
      simp only [loopAS]
      rw [times4 k _ rfl]
      cases st; simp only [updAS] at hk ⊢; congr 1; omega

/-- `fn_44`: `tw += 4·s2`. -/
theorem loop117 (st : AS) : Rn (.node 117) st { st with tw := st.tw + 4 * st.s2, s2 := 0 } := by
  have h := while_AS (n := 117) (r := 7) (b := .node 118) rfl (by omega)
    (fun st => { st with tw := st.tw + 4 }) (fun _ => rfl)
    (fun st => cont_cdr (p := dag254) (n := 118) (k := 0) rfl (add4 st) (Run.contS 1 _)) st.s2 st rfl
  rwa [times4 st.s2 st rfl] at h

/-- `node_110`: pop the theorem stack into `s1`. -/
theorem pop110 (st : AS) (hc : Clean st) :
    Rn (.node 160) st { st with ws := (Cantor.ofNat st.ws).2, s1 := (Cantor.ofNat st.ws).1 } :=
  rn_eq (seqAS (n := 160) rfl (loop116 st) (loop212 _)) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1 h2; simp [P_zero_zero])

/-- `cons`: `tw := Imp(top, tw)`, popping the stack. -/
theorem cons (st : AS) (hc : Clean st) :
    Rn (.node 119) st { st with tw := wim (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 } :=
  rn_eq (seqAS (n := 119) rfl (pop110 st hc) (seqAS (n := 120) rfl (pair162 _ _ rfl) (loop117 _))) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1 h2; simp [wim])

theorem cons_clean {st : AS} (hc : Clean st) :
    Clean { st with tw := wim (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 } := hc

theorem wel_m (st : AS) (hc : Clean st) :
    Rn (.node 181) st { st with tw := wel (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 } :=
  rn_eq (seqAS (n := 181) rfl (cons st hc) (inc_AS 1 (by omega) _)) (by simp [updAS, enc, wel, wim])

theorem wal_m (st : AS) (hc : Clean st) :
    Rn (.node 180) st { st with tw := wal (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 } :=
  rn_eq (seqAS (n := 180) rfl (cons st hc) (add2 _)) (by simp [wal, wim])

theorem weq_m (st : AS) (hc : Clean st) :
    Rn (.node 182) st { st with tw := weq (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 } :=
  rn_eq (seqAS (n := 182) rfl (cons st hc) (add3 _)) (by simp [weq, wim])

theorem ofNat_P (x y : Nat) : Cantor.ofNat (P x y) = (x, y) := unP_P x y

/-- `wn`: negation relative to F. -/
theorem wn_m (st : AS) (hc : Clean st) : Rn (.node 218) st { st with tw := wn st.tw } :=
  rn_eq (seqAS (n := 218) rfl (v1 st hc) (cons _ hc)) (by simp [ofNat_P, wn, F])

theorem wa_m (st : AS) (hc : Clean st) :
    Rn (.node 178) st { st with tw := wa (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 } :=
  rn_eq (seqAS (n := 178) rfl (wn_m st hc) (seqAS (n := 179) rfl (cons _ hc) (wn_m _ hc))) (by
    simp [wa])

theorem wex_m (st : AS) (hc : Clean st) :
    Rn (.node 183) st { st with tw := wex (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 } :=
  rn_eq (seqAS (n := 183) rfl (wn_m st hc) (seqAS (n := 184) rfl (wal_m _ hc) (wn_m _ hc))) (by
    simp [wex])

/-! ## Reads and pops -/

/-- `node_108`: unpair the proof list; the field goes to `s1`. -/
theorem read108 (st : AS) (hc : Clean st) :
    Rn (.node 158) st { st with pl := (Cantor.ofNat st.pl).2, s1 := (Cantor.ofNat st.pl).1 } :=
  rn_eq (seqAS (n := 158) rfl (loop115 st) (loop209 _)) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1 h2; simp [P_zero_zero])

theorem read_ac (st : AS) (hc : Clean st) :
    Rn (.node 174) st { st with pl := (Cantor.ofNat st.pl).2, ac := st.ac + (Cantor.ofNat st.pl).1 } :=
  rn_eq (seqAS (n := 174) rfl (read108 st hc) (loop201 _)) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1 h2; simp)

theorem read_p1 (st : AS) (hc : Clean st) :
    Rn (.node 175) st { st with pl := (Cantor.ofNat st.pl).2, p1 := st.p1 + (Cantor.ofNat st.pl).1 } :=
  rn_eq (seqAS (n := 175) rfl (read108 st hc) (loop205 _)) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1 h2; simp)

theorem read_p2 (st : AS) (hc : Clean st) :
    Rn (.node 176) st { st with pl := (Cantor.ofNat st.pl).2, p2 := st.p2 + (Cantor.ofNat st.pl).1 } :=
  rn_eq (seqAS (n := 176) rfl (read108 st hc) (loop207 _)) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1 h2; simp)

theorem pop_p2 (st : AS) (hc : Clean st) :
    Rn (.node 170) st { st with ws := (Cantor.ofNat st.ws).2, p2 := st.p2 + (Cantor.ofNat st.ws).1 } :=
  rn_eq (seqAS (n := 170) rfl (pop110 st hc) (loop207 _)) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1 h2; simp)

end SetTheory.BusyBeaver.ZFC.L2
