import BusyBeaver.ZFC.ArithmeticL2Lib254

set_option autoImplicit false

/-!
# Internal L2, part 2: stack and formula macros of the 219-node program

The internal counterpart of `L2Macros254`, in every model of `IΣ₁`. Every macro
is stated on a clean record (`s1 = s2 = 0`) and returns a clean record:

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

`P` is the internal Cantor pairing `cantor`, `unP` its projections
`first`/`second`, and the formula constructors are those of `ArithmeticCode254`
(`Imp(a,b) = 4·P(a,b)` and the others add their tags). All register values are
internal; the proofs follow `L2Macros254` constructor by constructor.
-/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticL2

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticDagRun RMDag
open ArithmeticControlFile (writeValue)
open ArithmeticCode254 (wim wel wal weq tagged)

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Negation relative to the falsity code `1`. -/
noncomputable def wn (a : V) : V := wim a 1
noncomputable def wa (a b : V) : V := wn (wim a (wn b))
noncomputable def wex (x a : V) : V := wn (wal x (wn a))

theorem rn_eq {e : RMDag.Edge} {s s1 s2 : AS V} (h : Rn e s s1) (he : s1 = s2) : Rn e s s2 :=
  he ▸ h

/-- A clean record. -/
def Clean (st : AS V) : Prop := st.s1 = 0 ∧ st.s2 = 0

/-! ## Pushes -/

theorem pushwff (st : AS V) (hc : Clean st) :
    Rn (.node 171) st { st with tw := 0, ws := cantor st.tw st.ws } :=
  rn_eq (R.seq (n := 171) rfl (loop216 st) (R.seq (n := 172) rfl (loop217 _)
    (R.seq (n := 173) rfl (pair162 _) (loop212 _)))) (by
      obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1; subst h2; simp)

theorem v1 (st : AS V) (hc : Clean st) :
    Rn (.node 177) st { st with tw := 1, ws := cantor st.tw st.ws } :=
  rn_eq (R.seq (n := 177) rfl (pushwff st hc) (inc_AS 1 (by omega) _)) (by simp [updAS, field])

theorem par1 (st : AS V) (hc : Clean st) :
    Rn (.node 166) st { st with tw := st.p1, ws := cantor st.tw st.ws } :=
  rn_eq (R.seq (n := 166) rfl (pushwff st hc) (R.seq (n := 167) rfl (loop198 _) (loop205 _))) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1; subst h2; simp)

theorem par2 (st : AS V) (hc : Clean st) :
    Rn (.node 121) st { st with tw := st.p2, ws := cantor st.tw st.ws } :=
  rn_eq (R.seq (n := 121) rfl (pushwff st hc) (R.seq (n := 122) rfl (loop200 _) (loop207 _))) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1; subst h2; simp)

theorem par3 (st : AS V) (hc : Clean st) :
    Rn (.node 168) st { st with tw := st.ac, ws := cantor st.tw st.ws } :=
  rn_eq (R.seq (n := 168) rfl (pushwff st hc) (R.seq (n := 169) rfl (loop193 _) (loop201 _))) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1; subst h2; simp)

/-! ## Constructors -/

theorem add2 (st : AS V) : Rn (.node 159) st { st with tw := st.tw + 2 } :=
  rn_eq (R.seq (n := 159) rfl (inc_AS 1 (by omega) st) (inc_AS 1 (by omega) _)) (by
    cases st; simp only [updAS, field]; congr 1; ring)

theorem add3 (st : AS V) : Rn (.node 157) st { st with tw := st.tw + 3 } :=
  rn_eq (R.seq (n := 157) rfl (add2 st) (inc_AS 1 (by omega) _)) (by
    cases st; simp only [updAS, field]; congr 1; ring)

theorem add4 (st : AS V) : Rn (.node 156) st { st with tw := st.tw + 4 } :=
  rn_eq (R.seq (n := 156) rfl (add3 st) (inc_AS 1 (by omega) _)) (by
    cases st; simp only [updAS, field]; congr 1; ring)

theorem lin_definable (a b : V) : 𝚺₁-Function₁[V] (fun t => a + b * t) := by definability

/-- `fn_44`: `tw += 4·s2`. -/
theorem loop117 (st : AS V) : Rn (.node 117) st { st with tw := st.tw + 4 * st.s2, s2 := 0 } := by
  let Gr : V → AS V := fun t => { st with tw := st.tw + 4 * t, s2 := st.s2 - t }
  let x0 : V := enc st
  -- logical tw and s2 are the physical fields 2 and 5
  let G : V → V := fun t =>
    writeValue ((5 : Nat) : V) (st.s2 - t) (writeValue ((2 : Nat) : V) (st.tw + 4 * t) x0)
  have hG : ∀ t, G t = enc (Gr t) := by
    intro t
    show lupd (lupd (enc st) 1 (st.tw + 4 * t)) 7 (st.s2 - t) = enc (Gr t)
    rw [lupd_enc _ 1 (by omega), lupd_enc _ 7 (by omega)]
    rfl
  haveI : 𝚺₁-Function₁[V] G :=
    write2_definable _ _ (fun t => st.s2 - t) (fun t => st.tw + 4 * t) x0
      (sub_definable st.s2) (lin_definable st.tw 4)
  have hpass : ∀ t, t < st.s2 → IR (.decnz 7) (G t) .normal (enc { (Gr t) with s2 := st.s2 - t - 1 }) ∧
      IR (.node 118) (enc { (Gr t) with s2 := st.s2 - t - 1 }) (.cont 1) (G (t+1)) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [hG]
      exact decPos_AS 7 (by omega) (Gr t) (st.s2 - t - 1)
        (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm
    · rw [hG]
      have h := R.cont_cdr (n := 118) (k := 0) rfl (add4 { (Gr t) with s2 := st.s2 - t - 1 })
        (R.contS 1 _)
      have e : ({ ({ (Gr t) with s2 := st.s2 - t - 1 } : AS V) with
          tw := ({ (Gr t) with s2 := st.s2 - t - 1 } : AS V).tw + 4 } : AS V) = Gr (t+1) := by
        simp only [Gr, tsub_tsub]
        congr 1
        ring
      rwa [e] at h
  have hfin : IR (.node 117) (G st.s2) .normal (G st.s2) := by
    rw [hG]
    exact R.skip (n := 117) rfl (decZero_AS 7 (by omega) (Gr st.s2) (by simp only [Gr, tsub_self]; rfl))
  have hit := R.iterate (n := 117) rfl G (fun t => enc { (Gr t) with s2 := st.s2 - t - 1 }) st.s2
    hpass hfin
  have hG0 : G 0 = enc st := by
    rw [hG]
    congr 1
    simp only [Gr, mul_zero, add_zero, tsub_zero]
  rw [hG0, hG] at hit
  simpa only [Gr, tsub_self] using hit

/-- `node_110`: pop the theorem stack into `s1`. -/
theorem pop110 (st : AS V) (hc : Clean st) :
    Rn (.node 160) st { st with ws := second st.ws, s1 := first st.ws } :=
  rn_eq (R.seq (n := 160) rfl (loop116 st) (loop212 _)) (by
    obtain ⟨h1, h2⟩ := hc
    cases st; simp only at h1 h2; subst h1; subst h2
    simp [unpairAS, AS.withWSZero, cantor, triangle])

/-- `cons`: `tw := Imp(top, tw)`, popping the stack. -/
theorem cons (st : AS V) (hc : Clean st) :
    Rn (.node 119) st { st with tw := wim (first st.ws) st.tw, ws := second st.ws } :=
  rn_eq (R.seq (n := 119) rfl (pop110 st hc) (R.seq (n := 120) rfl (pair162 _) (loop117 _))) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1; subst h2
    simp [wim, tagged])

theorem wel_m (st : AS V) (hc : Clean st) :
    Rn (.node 181) st { st with tw := wel (first st.ws) st.tw, ws := second st.ws } :=
  rn_eq (R.seq (n := 181) rfl (cons st hc) (inc_AS 1 (by omega) _)) (by
    simp [updAS, field, wel, wim, tagged])

theorem wal_m (st : AS V) (hc : Clean st) :
    Rn (.node 180) st { st with tw := wal (first st.ws) st.tw, ws := second st.ws } :=
  rn_eq (R.seq (n := 180) rfl (cons st hc) (add2 _)) (by simp [wal, wim, tagged])

theorem weq_m (st : AS V) (hc : Clean st) :
    Rn (.node 182) st { st with tw := weq (first st.ws) st.tw, ws := second st.ws } :=
  rn_eq (R.seq (n := 182) rfl (cons st hc) (add3 _)) (by simp [weq, wim, tagged])

/-- `wn`: negation relative to the falsity code. -/
theorem wn_m (st : AS V) (hc : Clean st) : Rn (.node 218) st { st with tw := wn st.tw } :=
  rn_eq (R.seq (n := 218) rfl (v1 st hc) (cons _ hc)) (by simp [wn])

theorem wa_m (st : AS V) (hc : Clean st) :
    Rn (.node 178) st { st with tw := wa (first st.ws) st.tw, ws := second st.ws } :=
  rn_eq (R.seq (n := 178) rfl (wn_m st hc) (R.seq (n := 179) rfl (cons _ hc) (wn_m _ hc))) (by
    simp [wa])

theorem wex_m (st : AS V) (hc : Clean st) :
    Rn (.node 183) st { st with tw := wex (first st.ws) st.tw, ws := second st.ws } :=
  rn_eq (R.seq (n := 183) rfl (wn_m st hc) (R.seq (n := 184) rfl (wal_m _ hc) (wn_m _ hc))) (by
    simp [wex])

/-! ## Reads and pops -/

/-- `node_108`: unpair the proof list; the field goes to `s1`. -/
theorem read108 (st : AS V) (hc : Clean st) :
    Rn (.node 158) st { st with pl := second st.pl, s1 := first st.pl } :=
  rn_eq (R.seq (n := 158) rfl (loop115 st) (loop209 _)) (by
    obtain ⟨h1, h2⟩ := hc
    cases st; simp only at h1 h2; subst h1; subst h2
    simp [unpairAS, AS.withPLZero, cantor, triangle])

theorem read_ac (st : AS V) (hc : Clean st) :
    Rn (.node 174) st { st with pl := second st.pl, ac := st.ac + first st.pl } :=
  rn_eq (R.seq (n := 174) rfl (read108 st hc) (loop201 _)) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1; subst h2; simp)

theorem read_p1 (st : AS V) (hc : Clean st) :
    Rn (.node 175) st { st with pl := second st.pl, p1 := st.p1 + first st.pl } :=
  rn_eq (R.seq (n := 175) rfl (read108 st hc) (loop205 _)) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1; subst h2; simp)

theorem read_p2 (st : AS V) (hc : Clean st) :
    Rn (.node 176) st { st with pl := second st.pl, p2 := st.p2 + first st.pl } :=
  rn_eq (R.seq (n := 176) rfl (read108 st hc) (loop207 _)) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1; subst h2; simp)

theorem pop_p2 (st : AS V) (hc : Clean st) :
    Rn (.node 170) st { st with ws := second st.ws, p2 := st.p2 + first st.ws } :=
  rn_eq (R.seq (n := 170) rfl (pop110 st hc) (loop207 _)) (by
    obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1; subst h2; simp)

end SetTheory.BusyBeaver.ZFC.ArithmeticL2
