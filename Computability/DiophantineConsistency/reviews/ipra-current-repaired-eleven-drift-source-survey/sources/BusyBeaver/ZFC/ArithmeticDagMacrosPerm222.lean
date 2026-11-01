import BusyBeaver.ZFC.ArithmeticDagControlPerm222

/-! Actual DagPerm data and formula-macro executions over arbitrary internal
IΣ1 values. The physical file is fixed, and every execution is proved for the
accepted actual table. Pairing/unpairing and macro algebra adapt the inspected
ArithmeticL2Lib254/ArithmeticL2Macros254 proof text; their old fixed-interpreter
semantic modules are not imported or invoked. Generic transfer/copy/clear loops
are reused from ArithmeticDagLoops. This file does not prove equality123,
dispatch/root execution, a 215 tape simulation, or a source/HA endpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace SetTheory.BusyBeaver.ZFC.ArithmeticDagMacrosPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticDagRun ArithmeticDagControlPerm222 RMDag
open ArithmeticControlFile (regValue fileValue writeValue liveValue reg_file file_reg reg_write
  write_defined live_defined)
open ArithmeticControlTable (write reg_write_same reg_write_other file_ext)
open ArithmeticCode254 (wim wel wal weq tagged)
open ArithmeticDagLoops (one_le_of_pos)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-! ## The nine registers -/

/-- The nine logical registers, in declaration order of `DagPerm`. -/
structure AS (V : Type*) where
  np : V
  tw : V
  ws : V
  ac : V
  p1 : V
  p2 : V
  s1 : V
  s2 : V
  pl : V

/-- Physical layout: field `p` holds logical register `physicalOrder[p]`. -/
noncomputable def enc (st : AS V) : V :=
  fileValue ![st.ws, st.pl, st.tw, st.p1, st.ac, st.s2, st.np, st.p2, st.s1]

/-- Logical register `r` of a record. -/
def field (st : AS V) : Nat → V
  | 0 => st.np | 1 => st.tw | 2 => st.ws | 3 => st.ac | 4 => st.p1
  | 5 => st.p2 | 6 => st.s1 | 7 => st.s2 | 8 => st.pl | _ => 0

/-- Update logical register `r`. -/
def updAS (st : AS V) : Nat → V → AS V
  | 0, v => { st with np := v } | 1, v => { st with tw := v } | 2, v => { st with ws := v }
  | 3, v => { st with ac := v } | 4, v => { st with p1 := v } | 5, v => { st with p2 := v }
  | 6, v => { st with s1 := v } | 7, v => { st with s2 := v } | 8, v => { st with pl := v }
  | _, _ => st

theorem lreg_enc (st : AS V) (r : Nat) (hr : r < 9) : lreg (enc st) r = field st r := by
  unfold lreg enc phys
  rw [reg_file]
  match r, hr with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl
  | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl

theorem reg_enc (st : AS V) (q : Fin 9) :
    regValue (enc st) q = ![st.ws, st.pl, st.tw, st.p1, st.ac, st.s2, st.np, st.p2, st.s1] q := by
  rw [enc, reg_file]

theorem reg_write' (p q : Fin 9) (v x : V) :
    regValue (write p v x) q = if p = q then v else regValue x q := by
  by_cases h : p = q
  · subst h; rw [reg_write_same, if_pos rfl]
  · rw [reg_write_other p q v x h, if_neg h]

theorem fin9_cases {P : Fin 9 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4)
    (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) : ∀ q, P q := by
  intro ⟨q, hq⟩
  match q, hq with
  | 0, _ => exact h0 | 1, _ => exact h1 | 2, _ => exact h2 | 3, _ => exact h3
  | 4, _ => exact h4 | 5, _ => exact h5 | 6, _ => exact h6 | 7, _ => exact h7
  | 8, _ => exact h8

theorem lupd_enc (st : AS V) (r : Nat) (hr : r < 9) (v : V) :
    lupd (enc st) r v = enc (updAS st r v) := by
  apply file_ext
  unfold lupd
  refine fin9_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
  · rw [reg_write', reg_enc, reg_enc]
    match r, hr with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl
    | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
@[simp] theorem field_updAS_self (st : AS V) (r : Nat) (hr : r < 9) (v : V) :
    field (updAS st r v) r = v := by
  match r, hr with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl
  | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl

/-! ## The internal structured run of the actual DagPerm program -/

/-- Structured run of the represented actual DagPerm path interpreter. -/
abbrev IR (e : RMDag.Edge) (x : V) (X : Exit) (y : V) : Prop :=
  IRun DagPerm.dagPerm rowsLit (ArithmeticDagControlPerm222.run (V := V)) e x X y

/-- Normal structured run between records. -/
abbrev Rn (e : RMDag.Edge) (st st' : AS V) : Prop := IR e (enc st) .normal (enc st')

namespace R

theorem run_zero (x : V) : ArithmeticDagControlPerm222.run 0 x = x := ArithmeticControlTable.controlRun_zero _ x
theorem run_add (t u x : V) : ArithmeticDagControlPerm222.run (t+u) x = ArithmeticDagControlPerm222.run u (ArithmeticDagControlPerm222.run t x) :=
  ArithmeticControlTable.controlRun_add _ t u x
theorem run_one (x : V) : ArithmeticDagControlPerm222.run 1 x = ArithmeticControlTable.stepValue table x :=
  ArithmeticControlTable.controlRun_one _ x

theorem inc (r : Nat) (x : V) : IR (.inc r) x .normal (lupd x r (lreg x r + 1)) :=
  run_inc run_one ArithmeticDagControlPerm222.spec r x
theorem decPos (r : Nat) (x v : V) (hv : lreg x r = v + 1) : IR (.decnz r) x .normal (lupd x r v) :=
  run_decPos run_one ArithmeticDagControlPerm222.spec r x v hv
theorem decZero (r : Nat) (x : V) (hz : lreg x r = 0) : IR (.decnz r) x (.brk 1) x :=
  run_decZero run_one ArithmeticDagControlPerm222.spec r x hz
theorem brk0 (x : V) : IR (.brk 0) x .normal x := run_brk0 run_one ArithmeticDagControlPerm222.spec x
theorem brkS (k : Nat) (x : V) : IR (.brk (k+1)) x (.brk (k+1)) x :=
  run_brkS run_one ArithmeticDagControlPerm222.spec k x
theorem contS (k : Nat) (x : V) : IR (.cont (k+1)) x (.cont (k+1)) x :=
  run_contS run_one ArithmeticDagControlPerm222.spec k x
variable {n : Nat} {a b : RMDag.Edge}

theorem seq (hn : DagPerm.dagPerm.nodes n = (a, b)) {x y z : V}
    (ha : IR a x .normal y) (hb : IR b y .normal z) : IR (.node n) x .normal z :=
  run_seq run_add hn ha hb
theorem skip (hn : DagPerm.dagPerm.nodes n = (a, b)) {x y : V}
    (ha : IR a x (.brk 1) y) : IR (.node n) x .normal y :=
  run_skip hn ha
theorem brk_cdr {k : Nat} (hn : DagPerm.dagPerm.nodes n = (a, b)) {x y z : V}
    (ha : IR a x .normal y) (hb : IR b y (.brk (k+1)) z) : IR (.node n) x (.brk (k+1)) z :=
  run_brk_cdr run_add hn ha hb
theorem cont_car {k : Nat} (hn : DagPerm.dagPerm.nodes n = (a, b)) {x y : V}
    (ha : IR a x (.cont (k+1)) y) : IR (.node n) x (.cont (k+1)) y :=
  run_cont_car hn ha
theorem cont_cdr {k : Nat} (hn : DagPerm.dagPerm.nodes n = (a, b)) {x y z : V}
    (ha : IR a x .normal y) (hb : IR b y (.cont (k+2)) z) : IR (.node n) x (.cont (k+1)) z :=
  run_cont_cdr run_add hn ha hb
theorem restart (hn : DagPerm.dagPerm.nodes n = (a, b)) {x y z w : V} {X : Exit}
    (ha : IR a x .normal y) (hb : IR b y (.cont 1) z) (hrest : IR (.node n) z X w) :
    IR (.node n) x X w :=
  run_restart run_add hn ha hb hrest

local instance run_definable : 𝚺₁-Function₂[V] (ArithmeticDagControlPerm222.run (V := V)) :=
  ArithmeticControlTable.controlRun_definable table

theorem iterate (hn : DagPerm.dagPerm.nodes n = (a, b)) (G H : V → V) [𝚺₁-Function₁[V] G] (N : V)
    (hpass : ∀ t, t < N → IR a (G t) .normal (H t) ∧ IR b (H t) (.cont 1) (G (t+1)))
    {X : Exit} {y : V} (hfin : IR (.node n) (G N) X y) : IR (.node n) (G 0) X y :=
  run_iterate run_zero run_add hn G H N hpass hfin

end R


local instance run_definable : 𝚺₁-Function₂[V] (ArithmeticDagControlPerm222.run (V := V)) :=
  ArithmeticControlTable.controlRun_definable table
local instance write_definable : 𝚺₁-Function₃[V] writeValue := write_defined.to_definable

/-! ## Concrete needed DagPerm loop instances -/

/-- `s1 → ac` -/
theorem loop201 (st : AS V) : Rn (.node 201) st { st with ac := st.ac + st.s1, s1 := 0 } := by
  have h := ArithmeticDagLoops.transfer (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one ArithmeticDagControlPerm222.spec (n := 201) (m := 202) (src := 6) (dst := 3) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 3 (by omega), lreg_enc st 6 (by omega), lupd_enc st 3 (by omega),
    lupd_enc _ 6 (by omega)] at h
  exact h

/-- `s1 → np` -/
theorem loop203 (st : AS V) : Rn (.node 203) st { st with np := st.np + st.s1, s1 := 0 } := by
  have h := ArithmeticDagLoops.transfer (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one ArithmeticDagControlPerm222.spec (n := 203) (m := 204) (src := 6) (dst := 0) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 0 (by omega), lreg_enc st 6 (by omega), lupd_enc st 0 (by omega),
    lupd_enc _ 6 (by omega)] at h
  exact h

/-- `s1 → p1` -/
theorem loop205 (st : AS V) : Rn (.node 205) st { st with p1 := st.p1 + st.s1, s1 := 0 } := by
  have h := ArithmeticDagLoops.transfer (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one ArithmeticDagControlPerm222.spec (n := 205) (m := 206) (src := 6) (dst := 4) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 4 (by omega), lreg_enc st 6 (by omega), lupd_enc st 4 (by omega),
    lupd_enc _ 6 (by omega)] at h
  exact h

/-- `s1 → p2` -/
theorem loop207 (st : AS V) : Rn (.node 207) st { st with p2 := st.p2 + st.s1, s1 := 0 } := by
  have h := ArithmeticDagLoops.transfer (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one ArithmeticDagControlPerm222.spec (n := 207) (m := 191) (src := 6) (dst := 5) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 5 (by omega), lreg_enc st 6 (by omega), lupd_enc st 5 (by omega),
    lupd_enc _ 6 (by omega)] at h
  exact h

/-- `s1 → tw` -/
theorem loop208 (st : AS V) : Rn (.node 208) st { st with tw := st.tw + st.s1, s1 := 0 } := by
  have h := ArithmeticDagLoops.transfer (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one ArithmeticDagControlPerm222.spec (n := 208) (m := 186) (src := 6) (dst := 1) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 1 (by omega), lreg_enc st 6 (by omega), lupd_enc st 1 (by omega),
    lupd_enc _ 6 (by omega)] at h
  exact h

/-- `s2 → pl` -/
theorem loop209 (st : AS V) : Rn (.node 209) st { st with pl := st.pl + st.s2, s2 := 0 } := by
  have h := ArithmeticDagLoops.transfer (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one ArithmeticDagControlPerm222.spec (n := 209) (m := 210) (src := 7) (dst := 8) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 8 (by omega), lreg_enc st 7 (by omega), lupd_enc st 8 (by omega),
    lupd_enc _ 7 (by omega)] at h
  exact h

/-- `s2 → s1` -/
theorem loop211 (st : AS V) : Rn (.node 211) st { st with s1 := st.s1 + st.s2, s2 := 0 } := by
  have h := ArithmeticDagLoops.transfer (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one ArithmeticDagControlPerm222.spec (n := 211) (m := 185) (src := 7) (dst := 6) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 6 (by omega), lreg_enc st 7 (by omega), lupd_enc st 6 (by omega),
    lupd_enc _ 7 (by omega)] at h
  exact h

/-- `s2 → ws` -/
theorem loop212 (st : AS V) : Rn (.node 212) st { st with ws := st.ws + st.s2, s2 := 0 } := by
  have h := ArithmeticDagLoops.transfer (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one ArithmeticDagControlPerm222.spec (n := 212) (m := 213) (src := 7) (dst := 2) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 2 (by omega), lreg_enc st 7 (by omega), lupd_enc st 2 (by omega),
    lupd_enc _ 7 (by omega)] at h
  exact h


/-- `tw → s1` -/
theorem loop216 (st : AS V) : Rn (.node 216) st { st with s1 := st.s1 + st.tw, tw := 0 } := by
  have h := ArithmeticDagLoops.transfer (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one ArithmeticDagControlPerm222.spec (n := 216) (m := 185) (src := 1) (dst := 6) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 6 (by omega), lreg_enc st 1 (by omega), lupd_enc st 6 (by omega),
    lupd_enc _ 1 (by omega)] at h
  exact h

/-- `ws → tw` -/
theorem loop217 (st : AS V) : Rn (.node 217) st { st with tw := st.tw + st.ws, ws := 0 } := by
  have h := ArithmeticDagLoops.transfer (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one ArithmeticDagControlPerm222.spec (n := 217) (m := 186) (src := 2) (dst := 1) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 1 (by omega), lreg_enc st 2 (by omega), lupd_enc st 1 (by omega),
    lupd_enc _ 2 (by omega)] at h
  exact h


/-- `ac → s1, tw` -/
theorem loop193 (st : AS V) :
    Rn (.node 193) st { st with s1 := st.s1 + st.ac, tw := st.tw + st.ac, ac := 0 } := by
  have h := ArithmeticDagLoops.copy2 (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one ArithmeticDagControlPerm222.spec (n := 193) (m := 189) (m' := 190) (src := 3) (d1 := 6) (d2 := 1)
    rfl rfl rfl (by decide) (by decide) (by decide) (enc st)
  rw [lreg_enc st 6 (by omega), lreg_enc st 3 (by omega), lreg_enc st 1 (by omega),
    lupd_enc st 6 (by omega), lupd_enc _ 1 (by omega), lupd_enc _ 3 (by omega)] at h
  exact h

/-- `np → pl, s1` -/
theorem loop194 (st : AS V) :
    Rn (.node 194) st { st with pl := st.pl + st.np, s1 := st.s1 + st.np, np := 0 } := by
  have h := ArithmeticDagLoops.copy2 (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one ArithmeticDagControlPerm222.spec (n := 194) (m := 195) (m' := 196) (src := 0) (d1 := 8) (d2 := 6)
    rfl rfl rfl (by decide) (by decide) (by decide) (enc st)
  rw [lreg_enc st 8 (by omega), lreg_enc st 0 (by omega), lreg_enc st 6 (by omega),
    lupd_enc st 8 (by omega), lupd_enc _ 6 (by omega), lupd_enc _ 0 (by omega)] at h
  exact h

/-- `p1 → s1, tw` -/
theorem loop198 (st : AS V) :
    Rn (.node 198) st { st with s1 := st.s1 + st.p1, tw := st.tw + st.p1, p1 := 0 } := by
  have h := ArithmeticDagLoops.copy2 (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one ArithmeticDagControlPerm222.spec (n := 198) (m := 189) (m' := 190) (src := 4) (d1 := 6) (d2 := 1)
    rfl rfl rfl (by decide) (by decide) (by decide) (enc st)
  rw [lreg_enc st 6 (by omega), lreg_enc st 4 (by omega), lreg_enc st 1 (by omega),
    lupd_enc st 6 (by omega), lupd_enc _ 1 (by omega), lupd_enc _ 4 (by omega)] at h
  exact h

/-- `p2 → s1, tw` -/
theorem loop200 (st : AS V) :
    Rn (.node 200) st { st with s1 := st.s1 + st.p2, tw := st.tw + st.p2, p2 := 0 } := by
  have h := ArithmeticDagLoops.copy2 (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one ArithmeticDagControlPerm222.spec (n := 200) (m := 189) (m' := 190) (src := 5) (d1 := 6) (d2 := 1)
    rfl rfl rfl (by decide) (by decide) (by decide) (enc st)
  rw [lreg_enc st 6 (by omega), lreg_enc st 5 (by omega), lreg_enc st 1 (by omega),
    lupd_enc st 6 (by omega), lupd_enc _ 1 (by omega), lupd_enc _ 5 (by omega)] at h
  exact h

/-- `tw → s1, s2` -/
theorem loop215 (st : AS V) :
    Rn (.node 215) st { st with s1 := st.s1 + st.tw, s2 := st.s2 + st.tw, tw := 0 } := by
  have h := ArithmeticDagLoops.copy2 (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one ArithmeticDagControlPerm222.spec (n := 215) (m := 187) (m' := 188) (src := 1) (d1 := 6) (d2 := 7)
    rfl rfl rfl (by decide) (by decide) (by decide) (enc st)
  rw [lreg_enc st 6 (by omega), lreg_enc st 1 (by omega), lreg_enc st 7 (by omega),
    lupd_enc st 6 (by omega), lupd_enc _ 7 (by omega), lupd_enc _ 1 (by omega)] at h
  exact h


/-! ## Pairing -/

theorem decPos_AS (r : Nat) (hr : r < 9) (st : AS V) (v : V) (hv : field st r = v + 1) :
    IR (.decnz r) (enc st) .normal (enc (updAS st r v)) := by
  have h := R.decPos r (enc st) v (by rw [lreg_enc st r hr]; exact hv)
  rwa [lupd_enc st r hr] at h

theorem decZero_AS (r : Nat) (hr : r < 9) (st : AS V) (hz : field st r = 0) :
    IR (.decnz r) (enc st) (.brk 1) (enc st) :=
  R.decZero r (enc st) (by rw [lreg_enc st r hr]; exact hz)

theorem inc_AS (r : Nat) (hr : r < 9) (st : AS V) :
    IR (.inc r) (enc st) .normal (enc (updAS st r (field st r + 1))) := by
  have h := R.inc r (enc st)
  rwa [lreg_enc st r hr, lupd_enc st r hr] at h

/-- One restarting pass of the pairing loop's cdr (node 163). -/
theorem pass163 (u : AS V) (k : V) (hk : u.s1 = k + 1) :
    IR (.node 163) (enc u) (.cont 1) (enc { u with s1 := 0, s2 := u.s2 + 1, tw := u.tw + k }) := by
  have hdec := decPos_AS 6 (by omega) u k hk
  have hinc := inc_AS 7 (by omega) (updAS u 6 k)
  have h208 := loop208 (updAS (updAS u 6 k) 7 (field (updAS u 6 k) 7 + 1))
  have h165 := R.seq (n := 165) rfl hinc h208
  have h164 := R.cont_cdr (n := 164) (k := 1) rfl h165 (R.contS 2 _)
  have h163 := R.cont_cdr (n := 163) (k := 0) rfl hdec h164
  have e : ({ updAS (updAS u 6 k) 7 (field (updAS u 6 k) 7 + 1) with
      tw := (updAS (updAS u 6 k) 7 (field (updAS u 6 k) 7 + 1)).tw +
        (updAS (updAS u 6 k) 7 (field (updAS u 6 k) 7 + 1)).s1, s1 := 0 } : AS V) =
      { u with s1 := 0, s2 := u.s2 + 1, tw := u.tw + k } := by
    cases u; rfl
  rw [e] at h163
  exact h163

/-- The pairing loop finishes once its cdr finds `s1 = 0`. -/
theorem finish162 (u : AS V) (h1 : u.s1 = 0) (h2 : u.tw = 0) : Rn (.node 162) u u := by
  have h215 := loop215 u
  have he : ({ u with s1 := u.s1 + u.tw, s2 := u.s2 + u.tw, tw := 0 } : AS V) = u := by
    cases u; simp only at h1 h2 ⊢; subst h1; subst h2; simp
  rw [he] at h215
  exact R.seq (n := 162) rfl h215 (R.skip (n := 163) rfl (decZero_AS 6 (by omega) u h1))

local instance cantor_definable : 𝚺₀-Function₂[V] cantor := cantor_defined.to_definable

theorem triangle_eq_cantor (s : V) : triangle s = cantor s 0 := by simp [cantor]

local instance triangle_definable : 𝚺₀-Function₁[V] triangle := by
  rw [show (triangle : V → V) = fun s => cantor s 0 from funext triangle_eq_cantor]
  definability

theorem tsub_add_shift {K A d : V} (h : A + d ≤ K) : K - (A + d) + d = K - A := by
  have hK : K = K - (A + d) + (A + d) := (tsub_add_cancel_of_le h).symm
  calc K - (A + d) + d = (K - (A + d) + d + A) - A := (add_tsub_cancel_right _ _).symm
    _ = K - A := by rw [add_assoc (K - (A + d)) d A, add_comm d A, ← hK]

theorem le_of_add_eq_zero_left {a b : V} (h : a + b = 0) : a = 0 :=
  le_antisymm (h ▸ le_self_add) (Arithmetic.zero_le a)

theorem write2_definable (a b : V) (f g : V → V) (x0 : V)
    (hf : 𝚺₁-Function₁[V] f) (hg : 𝚺₁-Function₁[V] g) :
    𝚺₁-Function₁[V] (fun t => writeValue a (f t) (writeValue b (g t) x0)) := by
  definability

theorem sub_definable (m : V) : 𝚺₁-Function₁[V] (fun t => m - t) := by definability

theorem sub_triangle_definable (K n : V) :
    𝚺₁-Function₁[V] (fun t => K - triangle (n - t)) := by definability

/-- `pair(scratch2, scratch1, topwff)`: `s2 += P(s1, tw)`, clearing both inputs. -/
theorem pair162 (st : AS V) :
    Rn (.node 162) st { st with s2 := st.s2 + cantor st.s1 st.tw, s1 := 0, tw := 0 } := by
  by_cases hz : st.s1 + st.tw = 0
  · have ha : st.s1 = 0 := le_of_add_eq_zero_left hz
    have hb : st.tw = 0 := le_of_add_eq_zero_left (by rwa [add_comm] at hz)
    have e : ({ st with s2 := st.s2 + cantor st.s1 st.tw, s1 := 0, tw := 0 } : AS V) = st := by
      cases st; simp only at ha hb ⊢; subst ha; subst hb; simp [cantor, triangle]
    rw [e]
    exact finish162 st ha hb
  -- at least one pass: n = m + 1
  set m := st.s1 + st.tw - 1 with hm
  have hn : st.s1 + st.tw = m + 1 :=
    (tsub_add_cancel_of_le (one_le_of_pos (lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm hz)))).symm
  set K := st.s2 + st.tw + 1 + triangle (m + 1) with hK
  -- the first pass
  have h215 := loop215 st
  have hp0 := pass163 { st with s1 := st.s1 + st.tw, s2 := st.s2 + st.tw, tw := 0 } m hn
  -- the file before pass `t ≥ 1` of the node
  let Gr : V → AS V := fun t => { st with s1 := 0, tw := m - t, s2 := K - triangle (m + 1 - t) }
  let Hr : V → AS V := fun t =>
    { st with s1 := m - t, tw := 0, s2 := K - triangle (m + 1 - t) + (m - t) }
  let x0 : V := lupd (enc st) 6 0
  -- logical tw and s2 are the physical fields 2 and 5
  let G : V → V := fun t =>
    writeValue ((5 : Nat) : V) (K - triangle (m + 1 - t)) (writeValue ((2 : Nat) : V) (m - t) x0)
  have hG : ∀ t, G t = enc (Gr t) := by
    intro t
    show lupd (lupd (lupd (enc st) 6 0) 1 (m - t)) 7 (K - triangle (m + 1 - t)) = enc (Gr t)
    rw [lupd_enc _ 6 (by omega), lupd_enc _ 1 (by omega), lupd_enc _ 7 (by omega)]
    rfl
  haveI : 𝚺₁-Function₁[V] G :=
    write2_definable _ _ (fun t => K - triangle (m + 1 - t)) (fun t => m - t) x0
      (sub_triangle_definable K (m + 1)) (sub_definable m)
  have hpass : ∀ t, t < m → IR (.node 215) (G t) .normal (enc (Hr t)) ∧
      IR (.node 163) (enc (Hr t)) (.cont 1) (G (t+1)) := by
    intro t ht
    have hjm : m - t = (m - t - 1) + 1 :=
      (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm
    refine ⟨?_, ?_⟩
    · rw [hG]
      have h := loop215 (Gr t)
      have e : ({ Gr t with s1 := (Gr t).s1 + (Gr t).tw, s2 := (Gr t).s2 + (Gr t).tw, tw := 0 } :
          AS V) = Hr t := by
        simp only [Gr, Hr, zero_add]
      rwa [e] at h
    · rw [hG]
      have h := pass163 (Hr t) (m - t - 1) hjm
      have e : ({ Hr t with s1 := 0, s2 := (Hr t).s2 + 1, tw := (Hr t).tw + (m - t - 1) } :
          AS V) = Gr (t+1) := by
        simp only [Hr, Gr, zero_add]
        congr 1
        · rw [tsub_tsub]
        · have hsub : m + 1 - (t + 1) = m - t := add_tsub_add_eq_tsub_right m 1 t
          have hT : triangle (m + 1 - t) = triangle (m - t) + (m - t + 1) := by
            rw [show m + 1 - t = (m - t) + 1 from by
              rw [add_comm m 1, add_tsub_assoc_of_le (le_of_lt ht), add_comm], triangle_succ,
              add_assoc]
          have hle : triangle (m - t) + (m - t + 1) ≤ K := by
            rw [← hT, hK]
            exact le_trans (triangle_mono tsub_le_self) le_add_self
          rw [hsub, hT, add_assoc, tsub_add_shift hle]
      rwa [e] at h
  have hfin : IR (.node 162) (G m) .normal (G m) := by
    rw [hG]
    exact finish162 (Gr m) rfl (by simp only [Gr, tsub_self])
  have hit := R.iterate (n := 162) rfl G (fun t => enc (Hr t)) m hpass hfin
  have hG0 : G 0 = enc { st with s1 := 0, s2 := st.s2 + st.tw + 1, tw := 0 + m } := by
    rw [hG]
    congr 1
    have hs : K - triangle (m + 1 - 0) = st.s2 + st.tw + 1 := by
      rw [tsub_zero, hK, add_tsub_cancel_right]
    simp only [Gr, tsub_zero, zero_add]
    rw [show K - triangle (m + 1) = st.s2 + st.tw + 1 by simpa using hs]
  rw [hG0] at hit
  have hres := R.restart (n := 162) rfl h215 hp0 hit
  have h1 : triangle (1 : V) = 1 := by
    have h := triangle_succ (0 : V)
    have h0 : triangle (0 : V) = 0 := by simp [triangle]
    simpa [h0] using h
  have hs2 : K - triangle (m + 1 - m) = st.s2 + cantor st.s1 st.tw := by
    rw [add_tsub_cancel_left, h1, hK, cantor, hn, add_right_comm (st.s2 + st.tw) 1,
      add_tsub_cancel_right, add_assoc, add_comm st.tw]
  have e : Gr m = { st with s2 := st.s2 + cantor st.s1 st.tw, s1 := 0, tw := 0 } := by
    simp only [Gr, tsub_self]
    rw [hs2]
  rw [hG m, e] at hres
  exact hres

/-! ## The unpair walk -/

/-- `(s1, s2) := unP m`. -/
noncomputable def unpairAS (st : AS V) (m : V) : AS V := { st with s1 := first m, s2 := second m }

def AS.withPLZero (st : AS V) : AS V := { st with pl := 0 }
def AS.withWSZero (st : AS V) : AS V := { st with ws := 0 }

theorem cantor_zero_succ (b : V) : cantor 0 b + 1 = cantor (b + 1) 0 := by
  simp only [cantor, zero_add, add_zero, triangle_succ]

theorem cantor_pos_succ (a b : V) : cantor (a + 1) b + 1 = cantor a (b + 1) := by
  simp only [cantor]
  rw [show a + 1 + b = a + b + 1 by ring, show a + (b + 1) = a + b + 1 by ring, add_assoc]

/-- One step of the unpair walk on `(s1, s2)`, as in `Cantor.ofNat`. -/
noncomputable def walkStep (st : AS V) : AS V :=
  if st.s1 = 0 then { st with s1 := st.s2 + 1, s2 := 0 }
  else { st with s1 := st.s1 - 1, s2 := st.s2 + 1 }

theorem walkStep_fields (u : AS V) :
    walkStep u = { u with s1 := first (cantor u.s1 u.s2 + 1), s2 := second (cantor u.s1 u.s2 + 1) } := by
  unfold walkStep
  split_ifs with h
  · rw [h, cantor_zero_succ, first_cantor, second_cantor]
  · have hv : u.s1 = (u.s1 - 1) + 1 :=
      (tsub_add_cancel_of_le (one_le_of_pos (lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm h)))).symm
    rw [hv, cantor_pos_succ, first_cantor, second_cantor, add_tsub_cancel_right]

/-- The shared loop body (node 154) performs one walk step and continues. -/
theorem body154 (st : AS V) : IR (.node 154) (enc st) (.cont 1) (enc (walkStep st)) := by
  have hinc := inc_AS 7 (by omega) st
  have h137 : Rn (.node 137) (updAS st 7 (field st 7 + 1)) (walkStep st) := by
    by_cases h0 : st.s1 = 0
    · have h138 := R.skip (n := 138) rfl (decZero_AS 6 (by omega) (updAS st 7 (field st 7 + 1)) h0)
      have h211 := loop211 (updAS st 7 (field st 7 + 1))
      have h := R.seq (n := 137) rfl h138 h211
      have e : ({ updAS st 7 (field st 7 + 1) with
          s1 := (updAS st 7 (field st 7 + 1)).s1 + (updAS st 7 (field st 7 + 1)).s2, s2 := 0 } : AS V)
          = walkStep st := by
        cases st
        simp only at h0
        subst h0
        simp [walkStep, updAS, field]
      rwa [e] at h
    · have hv : st.s1 = (st.s1 - 1) + 1 :=
        (tsub_add_cancel_of_le (one_le_of_pos (lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm h0)))).symm
      have hdec := decPos_AS 6 (by omega) (updAS st 7 (field st 7 + 1)) (st.s1 - 1) hv
      have h138 := R.brk_cdr (n := 138) (k := 0) rfl hdec (R.brkS 0 _)
      have h := R.skip (n := 137) rfl h138
      have e : updAS (updAS st 7 (field st 7 + 1)) 6 (st.s1 - 1) = walkStep st := by
        simp only [walkStep, if_neg h0]
        rfl
      rwa [e] at h
  have h155 := R.seq (n := 155) rfl hinc h137
  exact R.cont_cdr (n := 154) (k := 0) rfl h155 (R.contS 1 _)

theorem write3_definable (a b c : V) (f g h : V → V) (x0 : V)
    (hf : 𝚺₁-Function₁[V] f) (hg : 𝚺₁-Function₁[V] g) (hh : 𝚺₁-Function₁[V] h) :
    𝚺₁-Function₁[V] (fun t => writeValue a (f t) (writeValue b (g t) (writeValue c (h t) x0))) := by
  definability

local instance first_definable : 𝚺₀-Function₁[V] first := first_defined.to_definable
local instance second_definable : 𝚺₀-Function₁[V] second := second_defined.to_definable

theorem first_add_definable (M : V) : 𝚺₁-Function₁[V] (fun t => first (M + t)) := by definability
theorem second_add_definable (M : V) : 𝚺₁-Function₁[V] (fun t => second (M + t)) := by definability

/-- `fn_14`: unpair `pl` into `(s1, s2)`. -/
theorem loop115 (st : AS V) :
    Rn (.node 115) st (unpairAS st (cantor st.s1 st.s2 + st.pl)).withPLZero := by
  set M := cantor st.s1 st.s2
  set v := st.pl
  let Wr : V → AS V := fun t => { st with pl := v - t, s1 := first (M + t), s2 := second (M + t) }
  let x0 : V := enc st
  let G : V → V := fun t => writeValue ((1 : Nat) : V) (v - t)
    (writeValue ((5 : Nat) : V) (second (M + t)) (writeValue ((8 : Nat) : V) (first (M + t)) x0))
  have hG : ∀ t, G t = enc (Wr t) := by
    intro t
    show lupd (lupd (lupd (enc st) 6 (first (M + t))) 7 (second (M + t))) 8 (v - t) = enc (Wr t)
    rw [lupd_enc _ 6 (by omega), lupd_enc _ 7 (by omega), lupd_enc _ 8 (by omega)]
    rfl
  haveI : 𝚺₁-Function₁[V] G :=
    write3_definable _ _ _ (fun t => v - t) (fun t => second (M + t)) (fun t => first (M + t)) x0
      (sub_definable v) (second_add_definable M) (first_add_definable M)
  have hpass : ∀ t, t < v → IR (.decnz 8) (G t) .normal (enc { (Wr t) with pl := v - t - 1 }) ∧
      IR (.node 154) (enc { (Wr t) with pl := v - t - 1 }) (.cont 1) (G (t+1)) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [hG]
      exact decPos_AS 8 (by omega) (Wr t) (v - t - 1)
        (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm
    · rw [hG]
      have h := body154 { (Wr t) with pl := v - t - 1 }
      have e : walkStep { (Wr t) with pl := v - t - 1 } = Wr (t+1) := by
        rw [walkStep_fields]
        simp only [Wr, cantor_projections, add_assoc, tsub_tsub]
      rwa [e] at h
  have hfin : IR (.node 115) (G v) .normal (G v) := by
    rw [hG]
    exact R.skip (n := 115) rfl (decZero_AS 8 (by omega) (Wr v) (by simp only [Wr, tsub_self]; rfl))
  have hit := R.iterate (n := 115) rfl G (fun t => enc { (Wr t) with pl := v - t - 1 }) v hpass hfin
  have hG0 : G 0 = enc st := by
    rw [hG]
    congr 1
    simp only [Wr, add_zero, tsub_zero, M, first_cantor, second_cantor, v]
  rw [hG0, hG v] at hit
  simpa only [Wr, tsub_self, unpairAS, AS.withPLZero, AS.withWSZero] using hit

/-- `fn_41`: unpair `ws` into `(s1, s2)`. -/
theorem loop116 (st : AS V) :
    Rn (.node 116) st (unpairAS st (cantor st.s1 st.s2 + st.ws)).withWSZero := by
  set M := cantor st.s1 st.s2
  set v := st.ws
  let Wr : V → AS V := fun t => { st with ws := v - t, s1 := first (M + t), s2 := second (M + t) }
  let x0 : V := enc st
  let G : V → V := fun t => writeValue ((0 : Nat) : V) (v - t)
    (writeValue ((5 : Nat) : V) (second (M + t)) (writeValue ((8 : Nat) : V) (first (M + t)) x0))
  have hG : ∀ t, G t = enc (Wr t) := by
    intro t
    show lupd (lupd (lupd (enc st) 6 (first (M + t))) 7 (second (M + t))) 2 (v - t) = enc (Wr t)
    rw [lupd_enc _ 6 (by omega), lupd_enc _ 7 (by omega), lupd_enc _ 2 (by omega)]
    rfl
  haveI : 𝚺₁-Function₁[V] G :=
    write3_definable _ _ _ (fun t => v - t) (fun t => second (M + t)) (fun t => first (M + t)) x0
      (sub_definable v) (second_add_definable M) (first_add_definable M)
  have hpass : ∀ t, t < v → IR (.decnz 2) (G t) .normal (enc { (Wr t) with ws := v - t - 1 }) ∧
      IR (.node 154) (enc { (Wr t) with ws := v - t - 1 }) (.cont 1) (G (t+1)) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [hG]
      exact decPos_AS 2 (by omega) (Wr t) (v - t - 1)
        (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm
    · rw [hG]
      have h := body154 { (Wr t) with ws := v - t - 1 }
      have e : walkStep { (Wr t) with ws := v - t - 1 } = Wr (t+1) := by
        rw [walkStep_fields]
        simp only [Wr, cantor_projections, add_assoc, tsub_tsub]
      rwa [e] at h
  have hfin : IR (.node 116) (G v) .normal (G v) := by
    rw [hG]
    exact R.skip (n := 116) rfl (decZero_AS 2 (by omega) (Wr v) (by simp only [Wr, tsub_self]; rfl))
  have hit := R.iterate (n := 116) rfl G (fun t => enc { (Wr t) with ws := v - t - 1 }) v hpass hfin
  have hG0 : G 0 = enc st := by
    rw [hG]
    congr 1
    simp only [Wr, add_zero, tsub_zero, M, first_cantor, second_cantor, v]
  rw [hG0, hG v] at hit
  simpa only [Wr, tsub_self, unpairAS, AS.withPLZero, AS.withWSZero] using hit


/-! ## Actual formula and stack macros -/
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

/-- `node160`: pop the theorem stack into `s1`. -/
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

/-- `node158`: unpair the proof list; the field goes to `s1`. -/
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


/-! ## Actual fetch -/
/-- The actual rotated loop increments `np` before its zero test, so even a
zero scratch counter contributes one. Its internal invariant is `np+t,s1-t`;
this is not the historical transfer-then-increment control tree. -/
theorem loop136 (st : AS V) :
    Rn (.node 136) st { st with np := st.np + st.s1 + 1, s1 := 0 } := by
  let Gr : V → AS V := fun t => { st with np := st.np + t, s1 := st.s1 - t }
  let Hr : V → AS V := fun t => { st with np := st.np + t + 1, s1 := st.s1 - t }
  let G : V → V := fun t =>
    writeValue ((6 : Nat) : V) (st.np + t)
      (writeValue ((8 : Nat) : V) (st.s1 - t) (enc st))
  have hG : ∀ t, G t = enc (Gr t) := by
    intro t
    show lupd (lupd (enc st) 6 (st.s1 - t)) 0 (st.np + t) = enc (Gr t)
    rw [lupd_enc _ 6 (by omega), lupd_enc _ 0 (by omega)]
    rfl
  have hadd : 𝚺₁-Function₁[V] (fun t => st.np + t) := by definability
  haveI : 𝚺₁-Function₁[V] G :=
    write2_definable _ _ _ _ (enc st) hadd (sub_definable st.s1)
  have hpass : ∀ t, t < st.s1 → IR (.inc 0) (G t) .normal (enc (Hr t)) ∧
      IR (.node 300) (enc (Hr t)) (.cont 1) (G (t + 1)) := by
    intro t ht
    rw [hG, hG]
    refine ⟨inc_AS 0 (by omega) (Gr t), ?_⟩
    have hsub : st.s1 - t = (st.s1 - t - 1) + 1 :=
      (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm
    have hd := decPos_AS 6 (by omega) (Hr t) (st.s1 - t - 1) hsub
    have h := R.cont_cdr (n := 300) (k := 0) rfl hd (R.contS 1 _)
    have he : updAS (Hr t) 6 (st.s1 - t - 1) = Gr (t + 1) := by
      simp only [updAS, Gr, Hr, add_assoc, tsub_tsub]
    rwa [he] at h
  have hfin : IR (.node 136) (G st.s1) .normal
      (enc { st with np := st.np + st.s1 + 1, s1 := 0 }) := by
    rw [hG]
    have hi := inc_AS 0 (by omega) (Gr st.s1)
    have hz := decZero_AS 6 (by omega) (Hr st.s1) (by simp [Hr, field])
    have h := R.seq (n := 136) rfl hi (R.skip (n := 300) rfl hz)
    simpa only [Hr, tsub_self] using h
  have h := R.iterate (n := 136) rfl G (fun t => enc (Hr t)) st.s1 hpass hfin
  rw [hG] at h
  simpa only [Gr, add_zero, tsub_zero] using h

/-- The fetch (node 133): a nonzero proof list is decremented; an exhausted
one loads the next candidate. -/
theorem fetch_pos (st : AS V) (v : V) (hv : st.pl = v + 1) : Rn (.node 133) st { st with pl := v } := by
  have hdec := decPos_AS 8 (by omega) st v hv
  have h134 := R.brk_cdr (n := 134) (k := 0) rfl hdec (R.brkS 0 _)
  exact R.skip (n := 133) rfl h134

theorem fetch_zero (st : AS V) (hpl : st.pl = 0) (h1 : st.s1 = 0) :
    Rn (.node 133) st { st with pl := st.np, np := st.np + 1 } := by
  have h134 : Rn (.node 134) st st := R.skip (n := 134) rfl (decZero_AS 8 (by omega) st hpl)
  have h135 := R.seq (n := 135) rfl (loop194 st) (loop136 _)
  have := R.seq (n := 133) rfl h134 h135
  apply rn_eq this
  cases st; simp only at hpl h1; subst hpl; subst h1; simp


end SetTheory.BusyBeaver.ZFC.ArithmeticDagMacrosPerm222
