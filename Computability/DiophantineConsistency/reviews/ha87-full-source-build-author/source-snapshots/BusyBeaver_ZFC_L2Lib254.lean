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
  funext i; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

@[simp] theorem upd_tw (st : AS) (v : Nat) : upd (enc st) 1 v = enc { st with tw := v } := by
  funext i; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

@[simp] theorem upd_ws (st : AS) (v : Nat) : upd (enc st) 2 v = enc { st with ws := v } := by
  funext i; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

@[simp] theorem upd_ac (st : AS) (v : Nat) : upd (enc st) 3 v = enc { st with ac := v } := by
  funext i; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

@[simp] theorem upd_p1 (st : AS) (v : Nat) : upd (enc st) 4 v = enc { st with p1 := v } := by
  funext i; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

@[simp] theorem upd_p2 (st : AS) (v : Nat) : upd (enc st) 5 v = enc { st with p2 := v } := by
  funext i; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

@[simp] theorem upd_s1 (st : AS) (v : Nat) : upd (enc st) 6 v = enc { st with s1 := v } := by
  funext i; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

@[simp] theorem upd_s2 (st : AS) (v : Nat) : upd (enc st) 7 v = enc { st with s2 := v } := by
  funext i; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

@[simp] theorem upd_pl (st : AS) (v : Nat) : upd (enc st) 8 v = enc { st with pl := v } := by
  funext i; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [upd, enc]

/-! ## Loop instances -/

/-- `s1 → ac` -/
theorem loop201 (st : AS) : Rn (.node 201) st { st with ac := st.ac + st.s1, s1 := 0 } := by
  simpa [enc] using transfer (p := dag254) (n := 201) (m := 202) (src := 6) (dst := 3) rfl rfl
    (by decide) (enc st)

/-- `s1 → np` -/
theorem loop203 (st : AS) : Rn (.node 203) st { st with np := st.np + st.s1, s1 := 0 } := by
  simpa [enc] using transfer (p := dag254) (n := 203) (m := 204) (src := 6) (dst := 0) rfl rfl
    (by decide) (enc st)

/-- `s1 → p1` -/
theorem loop205 (st : AS) : Rn (.node 205) st { st with p1 := st.p1 + st.s1, s1 := 0 } := by
  simpa [enc] using transfer (p := dag254) (n := 205) (m := 206) (src := 6) (dst := 4) rfl rfl
    (by decide) (enc st)

/-- `s1 → p2` -/
theorem loop207 (st : AS) : Rn (.node 207) st { st with p2 := st.p2 + st.s1, s1 := 0 } := by
  simpa [enc] using transfer (p := dag254) (n := 207) (m := 191) (src := 6) (dst := 5) rfl rfl
    (by decide) (enc st)

/-- `s1 → tw` -/
theorem loop208 (st : AS) : Rn (.node 208) st { st with tw := st.tw + st.s1, s1 := 0 } := by
  simpa [enc] using transfer (p := dag254) (n := 208) (m := 186) (src := 6) (dst := 1) rfl rfl
    (by decide) (enc st)

/-- `s2 → pl` -/
theorem loop209 (st : AS) : Rn (.node 209) st { st with pl := st.pl + st.s2, s2 := 0 } := by
  simpa [enc] using transfer (p := dag254) (n := 209) (m := 210) (src := 7) (dst := 8) rfl rfl
    (by decide) (enc st)

/-- `s2 → s1` -/
theorem loop211 (st : AS) : Rn (.node 211) st { st with s1 := st.s1 + st.s2, s2 := 0 } := by
  simpa [enc] using transfer (p := dag254) (n := 211) (m := 185) (src := 7) (dst := 6) rfl rfl
    (by decide) (enc st)

/-- `s2 → ws` -/
theorem loop212 (st : AS) : Rn (.node 212) st { st with ws := st.ws + st.s2, s2 := 0 } := by
  simpa [enc] using transfer (p := dag254) (n := 212) (m := 213) (src := 7) (dst := 2) rfl rfl
    (by decide) (enc st)

/-- `p1 → p2` -/
theorem loop197 (st : AS) : Rn (.node 197) st { st with p2 := st.p2 + st.p1, p1 := 0 } := by
  simpa [enc] using transfer (p := dag254) (n := 197) (m := 191) (src := 4) (dst := 5) rfl rfl
    (by decide) (enc st)

/-- `tw → s1` -/
theorem loop216 (st : AS) : Rn (.node 216) st { st with s1 := st.s1 + st.tw, tw := 0 } := by
  simpa [enc] using transfer (p := dag254) (n := 216) (m := 185) (src := 1) (dst := 6) rfl rfl
    (by decide) (enc st)

/-- `ws → tw` -/
theorem loop217 (st : AS) : Rn (.node 217) st { st with tw := st.tw + st.ws, ws := 0 } := by
  simpa [enc] using transfer (p := dag254) (n := 217) (m := 186) (src := 2) (dst := 1) rfl rfl
    (by decide) (enc st)

/-- `ac → s1, s2` -/
theorem loop192 (st : AS) :
    Rn (.node 192) st { st with s1 := st.s1 + st.ac, s2 := st.s2 + st.ac, ac := 0 } := by
  simpa [enc] using copy2 (p := dag254) (n := 192) (m := 187) (m' := 188) (src := 3)
    (d1 := 6) (d2 := 7) rfl rfl rfl (by decide) (by decide) (by decide) (enc st)

/-- `ac → s1, tw` -/
theorem loop193 (st : AS) :
    Rn (.node 193) st { st with s1 := st.s1 + st.ac, tw := st.tw + st.ac, ac := 0 } := by
  simpa [enc] using copy2 (p := dag254) (n := 193) (m := 189) (m' := 190) (src := 3)
    (d1 := 6) (d2 := 1) rfl rfl rfl (by decide) (by decide) (by decide) (enc st)

/-- `np → pl, s1` -/
theorem loop194 (st : AS) :
    Rn (.node 194) st { st with pl := st.pl + st.np, s1 := st.s1 + st.np, np := 0 } := by
  simpa [enc] using copy2 (p := dag254) (n := 194) (m := 195) (m' := 196) (src := 0)
    (d1 := 8) (d2 := 6) rfl rfl rfl (by decide) (by decide) (by decide) (enc st)

/-- `p1 → s1, tw` -/
theorem loop198 (st : AS) :
    Rn (.node 198) st { st with s1 := st.s1 + st.p1, tw := st.tw + st.p1, p1 := 0 } := by
  simpa [enc] using copy2 (p := dag254) (n := 198) (m := 189) (m' := 190) (src := 4)
    (d1 := 6) (d2 := 1) rfl rfl rfl (by decide) (by decide) (by decide) (enc st)

/-- `p2 → s1, tw` -/
theorem loop200 (st : AS) :
    Rn (.node 200) st { st with s1 := st.s1 + st.p2, tw := st.tw + st.p2, p2 := 0 } := by
  simpa [enc] using copy2 (p := dag254) (n := 200) (m := 189) (m' := 190) (src := 5)
    (d1 := 6) (d2 := 1) rfl rfl rfl (by decide) (by decide) (by decide) (enc st)

/-- `tw → s1, s2` -/
theorem loop215 (st : AS) :
    Rn (.node 215) st { st with s1 := st.s1 + st.tw, s2 := st.s2 + st.tw, tw := 0 } := by
  simpa [enc] using copy2 (p := dag254) (n := 215) (m := 187) (m' := 188) (src := 1)
    (d1 := 6) (d2 := 7) rfl rfl rfl (by decide) (by decide) (by decide) (enc st)

/-- clear `p2` -/
theorem loop199 (st : AS) : Rn (.node 199) st { st with p2 := 0 } := by
  simpa [enc] using clear (p := dag254) (n := 199) (r := 5) rfl (enc st)

/-- clear `tw` -/
theorem loop214 (st : AS) : Rn (.node 214) st { st with tw := 0 } := by
  simpa [enc] using clear (p := dag254) (n := 214) (r := 1) rfl (enc st)

/-! ## Pairing and unpairing -/

theorem P_zero_zero : P 0 0 = 0 := by
  simp [P, Cantor.toNat, Cantor.tri]

/-- One triangular step: if `a + b = k + 1` then `P a b = P 0 k + b + 1`. -/
theorem P_step (a b k : Nat) (h : a + b = k + 1) : P a b = P 0 k + b + 1 := by
  simp only [P, Cantor.toNat]
  rw [h]
  simp only [Cantor.tri, Nat.zero_add]
  omega

/-- `pair(scratch2, scratch1, topwff)`: `s2 += P(s1, tw)`, clearing both inputs. -/
theorem pair162 : ∀ (n : Nat) (st : AS), st.s1 + st.tw = n →
    Rn (.node 162) st { st with s2 := st.s2 + P st.s1 st.tw, s1 := 0, tw := 0 }
  | 0, st, h => by
      have hz : enc { st with s1 := st.s1 + st.tw, s2 := st.s2 + st.tw, tw := 0 } 6 = 0 := by
        simp only [enc]; omega
      have h2 := skip (p := dag254) (n := 163) rfl (Run.decZero 6 _ hz)
      have := seq (p := dag254) (n := 162) rfl (loop215 st) h2
      have e : ({ st with s1 := st.s1 + st.tw, s2 := st.s2 + st.tw, tw := 0 } : AS) =
          { st with s2 := st.s2 + P st.s1 st.tw, s1 := 0, tw := 0 } := by
        obtain ⟨ha, hb⟩ : st.s1 = 0 ∧ st.tw = 0 := ⟨by omega, by omega⟩
        cases st; simp only at ha hb; subst ha hb; simp [P_zero_zero]
      rwa [e] at this
  | k + 1, st, h => by
      let st1 : AS := { st with s1 := st.s1 + st.tw, s2 := st.s2 + st.tw, tw := 0 }
      have h1 : Rn (.node 215) st st1 := loop215 st
      have hpos : enc st1 6 = k + 1 := by simp only [st1, enc]; omega
      let st2 : AS := { st1 with s1 := k }
      have hdec : Run dag254 (.decnz 6) (enc st1) .normal (enc st2) := by
        simpa [st2] using Run.decPos (p := dag254) 6 (enc st1) k hpos
      let st3 : AS := { st2 with s2 := st2.s2 + 1 }
      have hinc : Run dag254 (.inc 7) (enc st2) .normal (enc st3) := by
        simpa [st3, enc] using Run.inc (p := dag254) 7 (enc st2)
      let st4 : AS := { st3 with tw := st3.tw + st3.s1, s1 := 0 }
      have h208 : Rn (.node 208) st3 st4 := loop208 st3
      have h165 : Rn (.node 165) st2 st4 := seq (p := dag254) (n := 165) rfl hinc h208
      have h164 : Run dag254 (.node 164) (enc st2) (.cont 2) (enc st4) :=
        cont_cdr (p := dag254) (n := 164) (k := 1) rfl h165 (Run.contS 2 _)
      have h163 : Run dag254 (.node 163) (enc st1) (.cont 1) (enc st4) :=
        cont_cdr (p := dag254) (n := 163) (k := 0) rfl hdec h164
      have hrest := pair162 k st4 (by simp only [st4, st3, st2, st1]; omega)
      have := restart (p := dag254) (n := 162) rfl h1 h163 hrest
      have e : ({ st4 with s2 := st4.s2 + P st4.s1 st4.tw, s1 := 0, tw := 0 } : AS) =
          { st with s2 := st.s2 + P st.s1 st.tw, s1 := 0, tw := 0 } := by
        have hs := P_step st.s1 st.tw k h
        simp only [st4, st3, st2, st1, Nat.zero_add]
        rw [hs]
        congr 1
        omega
      rwa [e] at this

/-- One step of the unpair walk on `(s1, s2)`, as in `Cantor.ofNat`. -/
def walkStep (st : AS) : AS :=
  if st.s1 = 0 then { st with s1 := st.s2 + 1, s2 := 0 } else { st with s1 := st.s1 - 1, s2 := st.s2 + 1 }

/-- The shared loop body (node 154) performs one walk step and continues. -/
theorem body154 (st : AS) : Run dag254 (.node 154) (enc st) (.cont 1) (enc (walkStep st)) := by
  let st1 : AS := { st with s2 := st.s2 + 1 }
  have hinc : Run dag254 (.inc 7) (enc st) .normal (enc st1) := by
    simpa [st1, enc] using Run.inc (p := dag254) 7 (enc st)
  have h137 : Rn (.node 137) st1 (walkStep st) := by
    by_cases h0 : st.s1 = 0
    · have hz : enc st1 6 = 0 := by simp [st1, enc, h0]
      have h138 : Run dag254 (.node 138) (enc st1) .normal (enc st1) :=
        skip (p := dag254) (n := 138) rfl (Run.decZero 6 _ hz)
      have := seq (p := dag254) (n := 137) rfl h138 (loop211 st1)
      have e : ({ st1 with s1 := st1.s1 + st1.s2, s2 := 0 } : AS) = walkStep st := by
        simp [st1, walkStep, h0]
      rwa [e] at this
    · obtain ⟨v, hv⟩ : ∃ v, st.s1 = v + 1 := ⟨st.s1 - 1, by omega⟩
      have hp : enc st1 6 = v + 1 := by simp [st1, enc, hv]
      have h138 : Run dag254 (.node 138) (enc st1) (.brk 1) (upd (enc st1) 6 v) :=
        brk_cdr (p := dag254) (n := 138) (k := 0) rfl (Run.decPos 6 (enc st1) v hp) (Run.brkS 0 _)
      have := skip (p := dag254) (n := 137) rfl h138
      have e : upd (enc st1) 6 v = enc (walkStep st) := by
        simp [st1, walkStep, hv]
      rwa [e] at this
  have h155 : Rn (.node 155) st (walkStep st) := seq (p := dag254) (n := 155) rfl hinc h137
  exact cont_cdr (p := dag254) (n := 154) (k := 0) rfl h155 (Run.contS 1 _)

theorem walkStep_ofNat (st : AS) (m : Nat) (h : (st.s1, st.s2) = Cantor.ofNat m) :
    ((walkStep st).s1, (walkStep st).s2) = Cantor.ofNat (m + 1) := by
  simp only [Cantor.ofNat]
  rw [← h]
  unfold walkStep
  by_cases h0 : st.s1 = 0
  · simp [h0]
  · obtain ⟨v, hv⟩ : ∃ v, st.s1 = v + 1 := ⟨st.s1 - 1, by omega⟩
    simp [hv]

/-! ## Loops over the record -/

/-- Update one of the nine registers by index. -/
def updAS (st : AS) : Nat → Nat → AS
  | 0, v => { st with np := v }
  | 1, v => { st with tw := v }
  | 2, v => { st with ws := v }
  | 3, v => { st with ac := v }
  | 4, v => { st with p1 := v }
  | 5, v => { st with p2 := v }
  | 6, v => { st with s1 := v }
  | 7, v => { st with s2 := v }
  | 8, v => { st with pl := v }
  | _, _ => st

theorem upd_enc_AS (st : AS) (r v : Nat) (hr : r < 9) : upd (enc st) r v = enc (updAS st r v) := by
  match r, hr with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ => simp [updAS]

theorem enc_updAS_self (st : AS) (r v : Nat) (hr : r < 9) : enc (updAS st r v) r = v := by
  match r, hr with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ => rfl

/-- Iterated effect of a loop whose body is `g` and whose counter is `r`. -/
def loopAS (g : AS → AS) (r : Nat) : Nat → AS → AS
  | 0, st => st
  | k + 1, st => loopAS g r k (g (updAS st r k))

theorem while_AS {n r : Nat} {b : Edge} (hn : dag254.nodes n = (.decnz r, b)) (hr : r < 9)
    (g : AS → AS) (hg : ∀ st, enc (g st) r = enc st r)
    (hbody : ∀ st, Run dag254 b (enc st) (.cont 1) (enc (g st))) :
    ∀ (k : Nat) (st : AS), enc st r = k → Rn (.node n) st (loopAS g r k st)
  | 0, st, hk => skip hn (.decZero r (enc st) hk)
  | k + 1, st, hk => by
      have hdec := Run.decPos (p := dag254) r (enc st) k hk
      rw [upd_enc_AS st r k hr] at hdec
      apply restart hn hdec (hbody _)
      apply while_AS hn hr g hg hbody k
      rw [hg, enc_updAS_self st r k hr]

/-! ## The unpair walk, `read` and `pop` -/

theorem P_walkStep (st : AS) : P (walkStep st).s1 (walkStep st).s2 = P st.s1 st.s2 + 1 := by
  have h := walkStep_ofNat st (P st.s1 st.s2) (by simp [P, Cantor.ofNat_toNat])
  have := congrArg Cantor.toNat h
  simp only [Cantor.toNat_ofNat] at this
  simpa [P] using this

theorem walk_pl : ∀ (k : Nat) (st : AS), st.pl = k →
    loopAS walkStep 8 k st = { st with pl := 0, s1 := (Cantor.ofNat (P st.s1 st.s2 + k)).1, s2 := (Cantor.ofNat (P st.s1 st.s2 + k)).2 }
  | 0, st, hk => by
      cases st; simp only at hk; subst hk
      simp [loopAS, P, Cantor.ofNat_toNat]
  | k + 1, st, hk => by
      simp only [loopAS]
      rw [walk_pl k _ (by unfold walkStep; split <;> rfl)]
      have hP : _ = P st.s1 st.s2 + 1 := P_walkStep (updAS st 8 k)
      rw [hP, show P st.s1 st.s2 + 1 + k = P st.s1 st.s2 + (k + 1) by omega]
      cases st
      simp only [updAS, walkStep]
      split <;> rfl

theorem walk_ws : ∀ (k : Nat) (st : AS), st.ws = k →
    loopAS walkStep 2 k st = { st with ws := 0, s1 := (Cantor.ofNat (P st.s1 st.s2 + k)).1, s2 := (Cantor.ofNat (P st.s1 st.s2 + k)).2 }
  | 0, st, hk => by
      cases st; simp only at hk; subst hk
      simp [loopAS, P, Cantor.ofNat_toNat]
  | k + 1, st, hk => by
      simp only [loopAS]
      rw [walk_ws k _ (by unfold walkStep; split <;> rfl)]
      have hP : _ = P st.s1 st.s2 + 1 := P_walkStep (updAS st 2 k)
      rw [hP, show P st.s1 st.s2 + 1 + k = P st.s1 st.s2 + (k + 1) by omega]
      cases st
      simp only [updAS, walkStep]
      split <;> rfl

/-- `fn_14`: unpair the proof list into `(s1, s2)`. -/
theorem loop115 (st : AS) : Rn (.node 115) st { st with pl := 0, s1 := (Cantor.ofNat (P st.s1 st.s2 + st.pl)).1, s2 := (Cantor.ofNat (P st.s1 st.s2 + st.pl)).2 } := by
  have h := while_AS (n := 115) (r := 8) (b := .node 154) rfl (by omega) walkStep
    (fun st => by unfold walkStep; split <;> rfl) body154 st.pl st rfl
  rwa [walk_pl st.pl st rfl] at h

/-- `fn_41`: unpair the theorem stack into `(s1, s2)`. -/
theorem loop116 (st : AS) : Rn (.node 116) st { st with ws := 0, s1 := (Cantor.ofNat (P st.s1 st.s2 + st.ws)).1, s2 := (Cantor.ofNat (P st.s1 st.s2 + st.ws)).2 } := by
  have h := while_AS (n := 116) (r := 2) (b := .node 154) rfl (by omega) walkStep
    (fun st => by unfold walkStep; split <;> rfl) body154 st.ws st rfl
  rwa [walk_ws st.ws st rfl] at h

end SetTheory.BusyBeaver.ZFC.L2
