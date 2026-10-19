import BusyBeaver.ZFC.ArithmeticDagRun
import BusyBeaver.ZFC.DagControl254
import BusyBeaver.ZFC.ArithmeticCode254
import BusyBeaver.ZFC.Dag254

set_option autoImplicit false

/-!
# Internal L2, part 1: registers, rules and loops of the 219-node program

The internal counterpart of `L2Lib254` in every model of `IΣ₁`. A nine-field
record of internal register values is encoded as a register file of the
represented dag254 path interpreter (`enc`; logical register `r` lives in the
physical field `physOf r`). `Rn e st st'` is the internal structured run
`ArithmeticDagRun.IRun` of edge `e` from `enc st` to a normal exit at
`enc st'`. The constructor lemmas of `ArithmeticDagRun` are specialized to this
interpreter (`R.inc` …), and the three loop shapes of the program — transfer,
two-way copy and clear — are proved for every internal counter value by the
internal iteration lemma `run_iterate`, then instantiated at every loop node of
`L2Lib254`.
-/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticL2

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticDagRun DagControl254 RMDag
open ArithmeticControlFile (regValue fileValue writeValue liveValue reg_file file_reg reg_write
  write_defined live_defined)
open ArithmeticControlTable (write reg_write_same reg_write_other file_ext)

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The nine registers -/

/-- The nine logical registers, in declaration order of `Dag254`. -/
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

/-! ## The internal structured run of the dag254 program -/

/-- Structured run of the represented dag254 path interpreter. -/
abbrev IR (e : RMDag.Edge) (x : V) (X : Exit) (y : V) : Prop :=
  IRun Dag254.dag254 rowsLit (DagControl254.run (V := V)) e x X y

/-- Normal structured run between records. -/
abbrev Rn (e : RMDag.Edge) (st st' : AS V) : Prop := IR e (enc st) .normal (enc st')

namespace R

theorem run_zero (x : V) : DagControl254.run 0 x = x := ArithmeticControlTable.controlRun_zero _ x
theorem run_add (t u x : V) : DagControl254.run (t+u) x = DagControl254.run u (DagControl254.run t x) :=
  ArithmeticControlTable.controlRun_add _ t u x
theorem run_one (x : V) : DagControl254.run 1 x = ArithmeticControlTable.stepValue table x :=
  ArithmeticControlTable.controlRun_one _ x

theorem inc (r : Nat) (x : V) : IR (.inc r) x .normal (lupd x r (lreg x r + 1)) :=
  run_inc run_one DagControl254.spec r x
theorem decPos (r : Nat) (x v : V) (hv : lreg x r = v + 1) : IR (.decnz r) x .normal (lupd x r v) :=
  run_decPos run_one DagControl254.spec r x v hv
theorem decZero (r : Nat) (x : V) (hz : lreg x r = 0) : IR (.decnz r) x (.brk 1) x :=
  run_decZero run_one DagControl254.spec r x hz
theorem brk0 (x : V) : IR (.brk 0) x .normal x := run_brk0 run_one DagControl254.spec x
theorem brkS (k : Nat) (x : V) : IR (.brk (k+1)) x (.brk (k+1)) x :=
  run_brkS run_one DagControl254.spec k x
theorem contS (k : Nat) (x : V) : IR (.cont (k+1)) x (.cont (k+1)) x :=
  run_contS run_one DagControl254.spec k x
theorem halt (x : V) : IR .halt x .halt x := run_halt run_one DagControl254.spec x

variable {n : Nat} {a b : RMDag.Edge}

theorem seq (hn : Dag254.dag254.nodes n = (a, b)) {x y z : V}
    (ha : IR a x .normal y) (hb : IR b y .normal z) : IR (.node n) x .normal z :=
  run_seq run_add hn ha hb
theorem skip (hn : Dag254.dag254.nodes n = (a, b)) {x y : V}
    (ha : IR a x (.brk 1) y) : IR (.node n) x .normal y :=
  run_skip hn ha
theorem halt_car (hn : Dag254.dag254.nodes n = (a, b)) {x y : V}
    (ha : IR a x .halt y) : IR (.node n) x .halt y :=
  run_halt_car hn ha
theorem halt_cdr (hn : Dag254.dag254.nodes n = (a, b)) {x y z : V}
    (ha : IR a x .normal y) (hb : IR b y .halt z) : IR (.node n) x .halt z :=
  run_halt_cdr run_add hn ha hb
theorem brk_cdr {k : Nat} (hn : Dag254.dag254.nodes n = (a, b)) {x y z : V}
    (ha : IR a x .normal y) (hb : IR b y (.brk (k+1)) z) : IR (.node n) x (.brk (k+1)) z :=
  run_brk_cdr run_add hn ha hb
theorem brk_car {k : Nat} (hn : Dag254.dag254.nodes n = (a, b)) {x y : V}
    (ha : IR a x (.brk (k+2)) y) : IR (.node n) x (.brk (k+1)) y :=
  run_brk_car hn ha
theorem cont_car {k : Nat} (hn : Dag254.dag254.nodes n = (a, b)) {x y : V}
    (ha : IR a x (.cont (k+1)) y) : IR (.node n) x (.cont (k+1)) y :=
  run_cont_car hn ha
theorem cont_cdr {k : Nat} (hn : Dag254.dag254.nodes n = (a, b)) {x y z : V}
    (ha : IR a x .normal y) (hb : IR b y (.cont (k+2)) z) : IR (.node n) x (.cont (k+1)) z :=
  run_cont_cdr run_add hn ha hb
theorem restart (hn : Dag254.dag254.nodes n = (a, b)) {x y z w : V} {X : Exit}
    (ha : IR a x .normal y) (hb : IR b y (.cont 1) z) (hrest : IR (.node n) z X w) :
    IR (.node n) x X w :=
  run_restart run_add hn ha hb hrest

local instance run_definable : 𝚺₁-Function₂[V] (DagControl254.run (V := V)) :=
  ArithmeticControlTable.controlRun_definable table

theorem iterate (hn : Dag254.dag254.nodes n = (a, b)) (G H : V → V) [𝚺₁-Function₁[V] G] (N : V)
    (hpass : ∀ t, t < N → IR a (G t) .normal (H t) ∧ IR b (H t) (.cont 1) (G (t+1)))
    {X : Exit} {y : V} (hfin : IR (.node n) (G N) X y) : IR (.node n) (G 0) X y :=
  run_iterate run_zero run_add hn G H N hpass hfin

end R

/-! ## The three loop shapes -/

local instance write_definable : 𝚺₁-Function₃[V] writeValue := write_defined.to_definable

theorem lreg_lupd_same (x v : V) (r : Nat) : lreg (lupd x r v) r = v := by
  simp only [lreg, lupd, reg_write_same]

theorem lreg_lupd_other (x v : V) (r s : Nat) (h : phys r ≠ phys s) :
    lreg (lupd x r v) s = lreg x s := by
  simp only [lreg, lupd]; exact reg_write_other _ _ _ _ h

theorem lupd_lreg (x : V) (r : Nat) : lupd x r (lreg x r) = x :=
  ArithmeticControlTable.write_same _ x

theorem lupd_write (x v : V) (r : Nat) : lupd x r v = writeValue ((phys r).val : V) v x := rfl

theorem lupd_lupd (x v w : V) (r : Nat) : lupd (lupd x r v) r w = lupd x r w := by
  apply file_ext; intro q
  simp only [lupd, reg_write']
  split_ifs <;> rfl

theorem lupd_comm (x v w : V) (r s : Nat) (h : phys r ≠ phys s) :
    lupd (lupd x r v) s w = lupd (lupd x s w) r v := by
  apply file_ext; intro q
  simp only [lupd, reg_write']
  split_ifs with h1 h2 h2
  · exact absurd (h2.trans h1.symm) h
  all_goals rfl

theorem one_le_of_pos {a : V} (h : 0 < a) : 1 ≤ a := by simpa using lt_iff_succ_le.mp h

/-- `while src > 0: src -= 1; dst += 1` behind one node: transfer `src` into `dst`. -/
theorem transfer {n m src dst : Nat} (hn : Dag254.dag254.nodes n = (.decnz src, .node m))
    (hm : Dag254.dag254.nodes m = (.inc dst, .cont 2)) (hsd : phys src ≠ phys dst) (x : V) :
    IR (.node n) x .normal (lupd (lupd x dst (lreg x dst + lreg x src)) src 0) := by
  have hds : phys dst ≠ phys src := fun h => hsd h.symm
  let G : V → V := fun t => lupd (lupd x dst (lreg x dst + t)) src (lreg x src - t)
  let H : V → V := fun t => lupd (G t) src (lreg x src - t - 1)
  haveI : 𝚺₁-Function₁[V] G := by
    simp only [G, lupd_write, lreg]
    definability
  have hG0 : G 0 = x := by
    simp only [G, add_zero, tsub_zero]
    rw [show lreg x src = lreg (lupd x dst (lreg x dst)) src from
      (lreg_lupd_other x _ dst src hds).symm, lupd_lreg, lupd_lreg]
  have hpass : ∀ t, t < lreg x src → IR (.decnz src) (G t) .normal (H t) ∧
      IR (.node m) (H t) (.cont 1) (G (t+1)) := by
    intro t ht
    refine ⟨R.decPos src (G t) (lreg x src - t - 1) ?_, ?_⟩
    · simp only [G, lreg_lupd_same]
      exact (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm
    · have hc := R.cont_cdr (k := 0) hm (R.inc dst (H t)) (R.contS 1 _)
      have key : lupd (H t) dst (lreg (H t) dst + 1) = G (t+1) := by
        simp only [H, G]
        rw [lreg_lupd_other _ _ _ _ hsd, lreg_lupd_other _ _ _ _ hsd, lreg_lupd_same, lupd_lupd,
          lupd_comm _ _ _ src dst hsd, lupd_lupd, add_assoc, tsub_tsub]
      rw [key] at hc
      exact hc
  have hfin : IR (.node n) (G (lreg x src)) .normal (G (lreg x src)) :=
    R.skip hn (R.decZero src _ (by simp only [G, lreg_lupd_same, tsub_self]))
  have h := R.iterate hn G H (lreg x src) hpass hfin
  rw [hG0] at h
  simpa only [G, tsub_self] using h

/-- A loop body `((inc d₁, inc d₂), continue 2)`: copy `src` into two registers. -/
theorem copy2 {n m m' src d1 d2 : Nat} (hn : Dag254.dag254.nodes n = (.decnz src, .node m))
    (hm : Dag254.dag254.nodes m = (.node m', .cont 2))
    (hm' : Dag254.dag254.nodes m' = (.inc d1, .inc d2))
    (h1 : phys src ≠ phys d1) (h2 : phys src ≠ phys d2) (h12 : phys d1 ≠ phys d2) (x : V) :
    IR (.node n) x .normal
      (lupd (lupd (lupd x d1 (lreg x d1 + lreg x src)) d2 (lreg x d2 + lreg x src)) src 0) := by
  have h1' : phys d1 ≠ phys src := fun h => h1 h.symm
  have h2' : phys d2 ≠ phys src := fun h => h2 h.symm
  have h12' : phys d2 ≠ phys d1 := fun h => h12 h.symm
  let G : V → V := fun t =>
    lupd (lupd (lupd x d1 (lreg x d1 + t)) d2 (lreg x d2 + t)) src (lreg x src - t)
  let H : V → V := fun t => lupd (G t) src (lreg x src - t - 1)
  haveI : 𝚺₁-Function₁[V] G := by
    simp only [G, lupd_write, lreg]
    definability
  have hG0 : G 0 = x := by
    simp only [G, add_zero, tsub_zero]
    rw [show lreg x src = lreg (lupd (lupd x d1 (lreg x d1)) d2 (lreg x d2)) src by
        rw [lreg_lupd_other _ _ _ _ h2', lreg_lupd_other _ _ _ _ h1'],
      lupd_lreg, show lreg x d2 = lreg (lupd x d1 (lreg x d1)) d2 from
        (lreg_lupd_other x _ d1 d2 h12).symm, lupd_lreg, lupd_lreg]
  have hpass : ∀ t, t < lreg x src → IR (.decnz src) (G t) .normal (H t) ∧
      IR (.node m) (H t) (.cont 1) (G (t+1)) := by
    intro t ht
    refine ⟨R.decPos src (G t) (lreg x src - t - 1) ?_, ?_⟩
    · simp only [G, lreg_lupd_same]
      exact (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm
    · have hin := R.seq hm' (R.inc d1 (H t)) (R.inc d2 _)
      have hc := R.cont_cdr (k := 0) hm hin (R.contS 1 _)
      have key : lupd (lupd (H t) d1 (lreg (H t) d1 + 1)) d2
          (lreg (lupd (H t) d1 (lreg (H t) d1 + 1)) d2 + 1) = G (t+1) := by
        simp only [H, G]
        rw [lreg_lupd_other _ _ _ _ h12, lreg_lupd_other _ _ _ _ h2, lreg_lupd_other _ _ _ _ h2,
          lreg_lupd_same, lreg_lupd_other _ _ _ _ h1, lreg_lupd_other _ _ _ _ h1,
          lreg_lupd_other _ _ _ _ h12', lreg_lupd_same, lupd_lupd]
        rw [lupd_comm _ _ _ src d1 h1, lupd_comm _ _ _ d2 d1 h12', lupd_lupd,
          lupd_comm _ _ _ src d2 h2, lupd_lupd, add_assoc, add_assoc, tsub_tsub]
      rw [key] at hc
      exact hc
  have hfin : IR (.node n) (G (lreg x src)) .normal (G (lreg x src)) :=
    R.skip hn (R.decZero src _ (by simp only [G, lreg_lupd_same, tsub_self]))
  have h := R.iterate hn G H (lreg x src) hpass hfin
  rw [hG0] at h
  simpa only [G, tsub_self] using h

/-- A loop `(decnz r, continue 1)` clears `r`. -/
theorem clear {n r : Nat} (hn : Dag254.dag254.nodes n = (.decnz r, .cont 1)) (x : V) :
    IR (.node n) x .normal (lupd x r 0) := by
  let G : V → V := fun t => lupd x r (lreg x r - t)
  haveI : 𝚺₁-Function₁[V] G := by
    simp only [G, lupd_write, lreg]
    definability
  have hG0 : G 0 = x := by simp only [G, tsub_zero]; exact lupd_lreg x r
  have hpass : ∀ t, t < lreg x r → IR (.decnz r) (G t) .normal (G (t+1)) ∧
      IR (.cont 1) (G (t+1)) (.cont 1) (G (t+1)) := by
    intro t ht
    refine ⟨?_, R.contS 0 _⟩
    have hd := R.decPos r (G t) (lreg x r - t - 1) (by
      simp only [G, lreg_lupd_same]
      exact (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm)
    have key : lupd (G t) r (lreg x r - t - 1) = G (t+1) := by
      simp only [G, lupd_lupd, tsub_tsub]
    rw [key] at hd
    exact hd
  have hfin : IR (.node n) (G (lreg x r)) .normal (G (lreg x r)) :=
    R.skip hn (R.decZero r _ (by simp only [G, lreg_lupd_same, tsub_self]))
  have h := R.iterate hn G (fun t => G (t+1)) (lreg x r) hpass hfin
  rw [hG0] at h
  simpa only [G, tsub_self] using h

/-! ## Loop instances (as in `L2Lib254`) -/

/-- `s1 → ac` -/
theorem loop201 (st : AS V) : Rn (.node 201) st { st with ac := st.ac + st.s1, s1 := 0 } := by
  have h := transfer (n := 201) (m := 202) (src := 6) (dst := 3) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 3 (by omega), lreg_enc st 6 (by omega), lupd_enc st 3 (by omega),
    lupd_enc _ 6 (by omega)] at h
  exact h

/-- `s1 → np` -/
theorem loop203 (st : AS V) : Rn (.node 203) st { st with np := st.np + st.s1, s1 := 0 } := by
  have h := transfer (n := 203) (m := 204) (src := 6) (dst := 0) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 0 (by omega), lreg_enc st 6 (by omega), lupd_enc st 0 (by omega),
    lupd_enc _ 6 (by omega)] at h
  exact h

/-- `s1 → p1` -/
theorem loop205 (st : AS V) : Rn (.node 205) st { st with p1 := st.p1 + st.s1, s1 := 0 } := by
  have h := transfer (n := 205) (m := 206) (src := 6) (dst := 4) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 4 (by omega), lreg_enc st 6 (by omega), lupd_enc st 4 (by omega),
    lupd_enc _ 6 (by omega)] at h
  exact h

/-- `s1 → p2` -/
theorem loop207 (st : AS V) : Rn (.node 207) st { st with p2 := st.p2 + st.s1, s1 := 0 } := by
  have h := transfer (n := 207) (m := 191) (src := 6) (dst := 5) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 5 (by omega), lreg_enc st 6 (by omega), lupd_enc st 5 (by omega),
    lupd_enc _ 6 (by omega)] at h
  exact h

/-- `s1 → tw` -/
theorem loop208 (st : AS V) : Rn (.node 208) st { st with tw := st.tw + st.s1, s1 := 0 } := by
  have h := transfer (n := 208) (m := 186) (src := 6) (dst := 1) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 1 (by omega), lreg_enc st 6 (by omega), lupd_enc st 1 (by omega),
    lupd_enc _ 6 (by omega)] at h
  exact h

/-- `s2 → pl` -/
theorem loop209 (st : AS V) : Rn (.node 209) st { st with pl := st.pl + st.s2, s2 := 0 } := by
  have h := transfer (n := 209) (m := 210) (src := 7) (dst := 8) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 8 (by omega), lreg_enc st 7 (by omega), lupd_enc st 8 (by omega),
    lupd_enc _ 7 (by omega)] at h
  exact h

/-- `s2 → s1` -/
theorem loop211 (st : AS V) : Rn (.node 211) st { st with s1 := st.s1 + st.s2, s2 := 0 } := by
  have h := transfer (n := 211) (m := 185) (src := 7) (dst := 6) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 6 (by omega), lreg_enc st 7 (by omega), lupd_enc st 6 (by omega),
    lupd_enc _ 7 (by omega)] at h
  exact h

/-- `s2 → ws` -/
theorem loop212 (st : AS V) : Rn (.node 212) st { st with ws := st.ws + st.s2, s2 := 0 } := by
  have h := transfer (n := 212) (m := 213) (src := 7) (dst := 2) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 2 (by omega), lreg_enc st 7 (by omega), lupd_enc st 2 (by omega),
    lupd_enc _ 7 (by omega)] at h
  exact h

/-- `p1 → p2` -/
theorem loop197 (st : AS V) : Rn (.node 197) st { st with p2 := st.p2 + st.p1, p1 := 0 } := by
  have h := transfer (n := 197) (m := 191) (src := 4) (dst := 5) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 5 (by omega), lreg_enc st 4 (by omega), lupd_enc st 5 (by omega),
    lupd_enc _ 4 (by omega)] at h
  exact h

/-- `tw → s1` -/
theorem loop216 (st : AS V) : Rn (.node 216) st { st with s1 := st.s1 + st.tw, tw := 0 } := by
  have h := transfer (n := 216) (m := 185) (src := 1) (dst := 6) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 6 (by omega), lreg_enc st 1 (by omega), lupd_enc st 6 (by omega),
    lupd_enc _ 1 (by omega)] at h
  exact h

/-- `ws → tw` -/
theorem loop217 (st : AS V) : Rn (.node 217) st { st with tw := st.tw + st.ws, ws := 0 } := by
  have h := transfer (n := 217) (m := 186) (src := 2) (dst := 1) rfl rfl (by decide) (enc st)
  rw [lreg_enc st 1 (by omega), lreg_enc st 2 (by omega), lupd_enc st 1 (by omega),
    lupd_enc _ 2 (by omega)] at h
  exact h

/-- `ac → s1, s2` -/
theorem loop192 (st : AS V) :
    Rn (.node 192) st { st with s1 := st.s1 + st.ac, s2 := st.s2 + st.ac, ac := 0 } := by
  have h := copy2 (n := 192) (m := 187) (m' := 188) (src := 3) (d1 := 6) (d2 := 7)
    rfl rfl rfl (by decide) (by decide) (by decide) (enc st)
  rw [lreg_enc st 6 (by omega), lreg_enc st 3 (by omega), lreg_enc st 7 (by omega),
    lupd_enc st 6 (by omega), lupd_enc _ 7 (by omega), lupd_enc _ 3 (by omega)] at h
  exact h

/-- `ac → s1, tw` -/
theorem loop193 (st : AS V) :
    Rn (.node 193) st { st with s1 := st.s1 + st.ac, tw := st.tw + st.ac, ac := 0 } := by
  have h := copy2 (n := 193) (m := 189) (m' := 190) (src := 3) (d1 := 6) (d2 := 1)
    rfl rfl rfl (by decide) (by decide) (by decide) (enc st)
  rw [lreg_enc st 6 (by omega), lreg_enc st 3 (by omega), lreg_enc st 1 (by omega),
    lupd_enc st 6 (by omega), lupd_enc _ 1 (by omega), lupd_enc _ 3 (by omega)] at h
  exact h

/-- `np → pl, s1` -/
theorem loop194 (st : AS V) :
    Rn (.node 194) st { st with pl := st.pl + st.np, s1 := st.s1 + st.np, np := 0 } := by
  have h := copy2 (n := 194) (m := 195) (m' := 196) (src := 0) (d1 := 8) (d2 := 6)
    rfl rfl rfl (by decide) (by decide) (by decide) (enc st)
  rw [lreg_enc st 8 (by omega), lreg_enc st 0 (by omega), lreg_enc st 6 (by omega),
    lupd_enc st 8 (by omega), lupd_enc _ 6 (by omega), lupd_enc _ 0 (by omega)] at h
  exact h

/-- `p1 → s1, tw` -/
theorem loop198 (st : AS V) :
    Rn (.node 198) st { st with s1 := st.s1 + st.p1, tw := st.tw + st.p1, p1 := 0 } := by
  have h := copy2 (n := 198) (m := 189) (m' := 190) (src := 4) (d1 := 6) (d2 := 1)
    rfl rfl rfl (by decide) (by decide) (by decide) (enc st)
  rw [lreg_enc st 6 (by omega), lreg_enc st 4 (by omega), lreg_enc st 1 (by omega),
    lupd_enc st 6 (by omega), lupd_enc _ 1 (by omega), lupd_enc _ 4 (by omega)] at h
  exact h

/-- `p2 → s1, tw` -/
theorem loop200 (st : AS V) :
    Rn (.node 200) st { st with s1 := st.s1 + st.p2, tw := st.tw + st.p2, p2 := 0 } := by
  have h := copy2 (n := 200) (m := 189) (m' := 190) (src := 5) (d1 := 6) (d2 := 1)
    rfl rfl rfl (by decide) (by decide) (by decide) (enc st)
  rw [lreg_enc st 6 (by omega), lreg_enc st 5 (by omega), lreg_enc st 1 (by omega),
    lupd_enc st 6 (by omega), lupd_enc _ 1 (by omega), lupd_enc _ 5 (by omega)] at h
  exact h

/-- `tw → s1, s2` -/
theorem loop215 (st : AS V) :
    Rn (.node 215) st { st with s1 := st.s1 + st.tw, s2 := st.s2 + st.tw, tw := 0 } := by
  have h := copy2 (n := 215) (m := 187) (m' := 188) (src := 1) (d1 := 6) (d2 := 7)
    rfl rfl rfl (by decide) (by decide) (by decide) (enc st)
  rw [lreg_enc st 6 (by omega), lreg_enc st 1 (by omega), lreg_enc st 7 (by omega),
    lupd_enc st 6 (by omega), lupd_enc _ 7 (by omega), lupd_enc _ 1 (by omega)] at h
  exact h

/-- clear `p2` -/
theorem loop199 (st : AS V) : Rn (.node 199) st { st with p2 := 0 } := by
  have h := clear (n := 199) (r := 5) rfl (enc st)
  rw [lupd_enc st 5 (by omega)] at h
  exact h

/-- clear `tw` -/
theorem loop214 (st : AS V) : Rn (.node 214) st { st with tw := 0 } := by
  have h := clear (n := 214) (r := 1) rfl (enc st)
  rw [lupd_enc st 1 (by omega)] at h
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

end SetTheory.BusyBeaver.ZFC.ArithmeticL2
