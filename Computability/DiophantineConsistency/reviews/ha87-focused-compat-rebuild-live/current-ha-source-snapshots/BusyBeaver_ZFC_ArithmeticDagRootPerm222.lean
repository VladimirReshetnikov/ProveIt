import BusyBeaver.ZFC.ArithmeticDagMacrosPerm222
import DiophantineConsistency.ArithmeticEnumStepPerm222

/-! Actual equality, AX word, dispatch and one complete root execution of DagPerm.
All machine counters range over arbitrary internal IΣ1 models. No structured
root execution, old254 runtime or standard-Nat simulation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace SetTheory.BusyBeaver.ZFC.ArithmeticDagRootPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticDagRun ArithmeticDagControlPerm222 RMDag
open ArithmeticDagMacrosPerm222
open ArithmeticControlFile (writeValue)
open ArithmeticCode254 (wim wel wal weq)
open ArithmeticDagLoops (one_le_of_pos)
open DiophantineConsistency.ArithmeticCommandStepPerm222
open DiophantineConsistency.ArithmeticCommandWordPerm222
open DiophantineConsistency.ArithmeticCommandFetchPerm222
open DiophantineConsistency.ArithmeticEnumStepPerm222 (enumValue execValue enum_live)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace H
 theorem halt (x : V) : IR .halt x .halt x :=
  run_halt R.run_one ArithmeticDagControlPerm222.spec x
 theorem halt_car {n : Nat} {a b : Edge} (hn : DagPerm.dagPerm.nodes n = (a,b))
    {x y : V} (ha : IR a x .halt y) : IR (.node n) x .halt y := run_halt_car hn ha
 theorem halt_cdr {n : Nat} {a b : Edge} (hn : DagPerm.dagPerm.nodes n = (a,b))
    {x y z : V} (ha : IR a x .normal y) (hb : IR b y .halt z) :
    IR (.node n) x .halt z := run_halt_cdr R.run_add hn ha hb
end H

local instance run_definable : 𝚺₁-Function₂[V] (ArithmeticDagControlPerm222.run (V := V)) :=
  ArithmeticControlTable.controlRun_definable table

/-! The actual new equality test: 123=(464,466), not the old124 loop. -/
theorem eqU_pos (st : AS V) (b : V) (hb : st.s1=b+1) :
    IR (.node 462) (enc st) (.cont 1) (enc {st with s1:=b}) :=
  R.cont_car (n:=462) rfl (R.cont_cdr (n:=461) (k:=0) rfl
    (decPos_AS 6 (by omega) st b hb) (R.contS 1 _))

theorem eqU_zero (st : AS V) (hb : st.s1=0) :
    IR (.node 462) (enc st) (.brk 1) (enc st) :=
  R.brk_cdr (n:=462) (k:=0) rfl
    (R.skip (n:=461) rfl (decZero_AS 6 (by omega) st hb)) (R.brkS 0 _)

/-- Cancellation runs for any internal number of joint decrements. -/
theorem cancel463 (st : AS V) (N : V) (hN1 : N≤st.s1) (hN2 : N≤st.p2)
    {X : Exit} {y : V}
    (hfin : IR (.node 463) (enc {st with s1:=st.s1-N,p2:=st.p2-N}) X y) :
    IR (.node 463) (enc st) X y := by
  let Gr : V → AS V := fun t => {st with s1:=st.s1-t,p2:=st.p2-t}
  let Hr : V → AS V := fun t => {st with s1:=st.s1-t,p2:=st.p2-t-1}
  let G : V → V := fun t => writeValue 7 (st.p2-t) (writeValue 8 (st.s1-t) (enc st))
  have hG : ∀t, G t=enc (Gr t) := by
    intro t
    show lupd (lupd (enc st) 6 (st.s1-t)) 5 (st.p2-t)=enc (Gr t)
    rw [lupd_enc _ 6 (by omega),lupd_enc _ 5 (by omega)]; rfl
  haveI : 𝚺₁-Function₁[V] G := write2_definable _ _ _ _ _ (sub_definable _) (sub_definable _)
  have hpass : ∀t, t<N → IR (.decnz 5) (G t) .normal (enc (Hr t)) ∧
      IR (.node 462) (enc (Hr t)) (.cont 1) (G (t+1)) := by
    intro t ht
    have h1 := tsub_pos_of_lt (lt_of_lt_of_le ht hN1)
    have h2 := tsub_pos_of_lt (lt_of_lt_of_le ht hN2)
    constructor
    · rw [hG]
      exact decPos_AS 5 (by omega) (Gr t) (st.p2-t-1)
        (tsub_add_cancel_of_le (one_le_of_pos h2)).symm
    · rw [hG]
      have hh := eqU_pos (Hr t) (st.s1-t-1)
        (tsub_add_cancel_of_le (one_le_of_pos h1)).symm
      simpa only [Hr,Gr,tsub_tsub] using hh
  have hh := R.iterate (n:=463) rfl G (fun t=>enc (Hr t)) N hpass (by rw [hG];exact hfin)
  simpa only [hG,Gr,tsub_zero] using hh

theorem eqA_le (st : AS V) (h : st.p2≤st.s1) :
    Rn (.node 463) st {st with s1:=st.s1-st.p2,p2:=0} := by
  apply cancel463 st st.p2 h le_rfl
  simpa only [tsub_self] using R.skip (n:=463) rfl
    (decZero_AS 5 (by omega) {st with s1:=st.s1-st.p2,p2:=0} rfl)

theorem eqA_lt (st : AS V) (h : st.s1<st.p2) :
    IR (.node 463) (enc st) (.brk 1) (enc {st with s1:=0,p2:=st.p2-st.s1-1}) := by
  apply cancel463 st st.s1 le_rfl (le_of_lt h)
  simp only [tsub_self]
  exact R.brk_cdr (n:=463) (k:=0) rfl
    (decPos_AS 5 (by omega) {st with s1:=0,p2:=st.p2-st.s1} (st.p2-st.s1-1)
      (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt h))).symm)
    (eqU_zero _ rfl)

theorem eqZ (st : AS V) : Rn (.node 465) st {st with p2:=0} := by
  have h := ArithmeticDagLoops.clear (p:=DagPerm.dagPerm) R.run_zero R.run_add R.run_one
    ArithmeticDagControlPerm222.spec (n:=465) (r:=5) rfl (enc st)
  rwa [lupd_enc _ 5 (by omega)] at h

/-- The second equality loop clears the remaining first counter and breaks. -/
theorem eqR_zero (st : AS V) (hp : st.p2=0) :
    IR (.node 466) (enc st) (.brk 1) (enc {st with s1:=0,p2:=0}) := by
  let Gr : V → AS V := fun t=>{st with s1:=st.s1-t,p2:=0}
  let G : V → V := fun t=>writeValue 7 0 (writeValue 8 (st.s1-t) (enc st))
  have hG : ∀t, G t=enc (Gr t) := by
    intro t
    show lupd (lupd (enc st) 6 (st.s1-t)) 5 0=enc (Gr t)
    rw [lupd_enc _ 6 (by omega),lupd_enc _ 5 (by omega)];rfl
  haveI : 𝚺₁-Function₁[V] G := write2_definable _ _ _ _ _ (by definability) (sub_definable _)
  have hpass : ∀t, t<st.s1 → IR (.node 465) (G t) .normal (G t) ∧
      IR (.node 462) (G t) (.cont 1) (G (t+1)) := by
    intro t ht
    simp only [hG]
    refine ⟨eqZ (Gr t),?_⟩
    have hh := eqU_pos (Gr t) (st.s1-t-1)
      (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm
    simpa only [Gr,tsub_tsub] using hh
  have hfin : IR (.node 466) (G st.s1) (.brk 1) (enc {st with s1:=0,p2:=0}) := by
    rw [hG];simp only [Gr,tsub_self]
    exact R.brk_cdr (n:=466) (k:=0) rfl (eqZ _) (eqU_zero _ rfl)
  have hh := R.iterate (n:=466) rfl G G st.s1 hpass hfin
  have he : G 0=enc st := by
    rw [hG];congr 1;cases st;simp_all [Gr]
  rwa [he] at hh

theorem eqR (st : AS V) :
    IR (.node 466) (enc st) (.brk 1) (enc {st with s1:=0,p2:=0}) := by
  by_cases hz : st.s1=0
  · have hh := R.brk_cdr (n:=466) (k:=0) rfl (eqZ st) (eqU_zero _ hz)
    simpa only [←hz] using hh
  · have hp := one_le_of_pos (lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm hz))
    exact R.restart (n:=466) rfl (eqZ st)
      (eqU_pos _ (st.s1-1) (tsub_add_cancel_of_le hp).symm) (eqR_zero _ rfl)

theorem ifeq_eq (st : AS V) (h : st.s1=st.p2) :
    Rn (.node 123) st {st with s1:=0,p2:=0} := by
  have ha := eqA_le st (le_of_eq h.symm)
  rw [h,tsub_self] at ha
  exact R.skip (n:=123) rfl (R.brk_cdr (n:=464) (k:=0) rfl ha
    (decZero_AS 6 (by omega) _ rfl))

theorem ifeq_ne (st : AS V) (h : st.s1≠st.p2) :
    IR (.node 123) (enc st) (.brk 1) (enc {st with s1:=0,p2:=0}) := by
  rcases lt_or_gt_of_ne h with hlt|hgt
  · exact R.brk_cdr (n:=123) (k:=0) rfl
      (R.skip (n:=464) rfl (eqA_lt st hlt)) (eqR _)
  · have hdec := decPos_AS 6 (by omega) {st with s1:=st.s1-st.p2,p2:=0}
      (st.s1-st.p2-1) (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt hgt))).symm
    exact R.brk_cdr (n:=123) (k:=0) rfl
      (R.seq (n:=464) rfl (eqA_le st (le_of_lt hgt)) hdec) (eqR _)

/-! Equality clients retain every input and clear exactly the actual registers. -/
theorem loop214 (st : AS V) : Rn (.node 214) st {st with tw:=0} := by
  have h := ArithmeticDagLoops.clear (p:=DagPerm.dagPerm) R.run_zero R.run_add R.run_one
    ArithmeticDagControlPerm222.spec (n:=214) (r:=1) rfl (enc st)
  rwa [lupd_enc _ 1 (by omega)] at h

/-- `if_eq (s1, param2, par1)` (node 130). -/
theorem ifeq_par1 (st : AS V) (h2 : st.s2 = 0) :
    Rn (.node 130) st (if st.s1 = st.p2
      then { st with s1 := 0, p2 := 0, tw := st.p1, ws := cantor st.tw st.ws }
      else { st with s1 := 0, p2 := 0 }) := by
  by_cases h : st.s1 = st.p2
  · rw [if_pos h]
    exact R.seq (n := 130) rfl (ifeq_eq st h) (par1 _ ⟨rfl, h2⟩)
  · rw [if_neg h]
    exact R.skip (n := 130) rfl (ifeq_ne st h)

/-- `if_eq (s1, param2, clear tw)` (node 131), the gate test. -/
theorem ifeq_clear (st : AS V) :
    Rn (.node 131) st (if st.s1 = st.p2
      then { st with s1 := 0, p2 := 0, tw := 0 } else { st with s1 := 0, p2 := 0 }) := by
  by_cases h : st.s1 = st.p2
  · rw [if_pos h]
    exact R.seq (n := 131) rfl (ifeq_eq st h) (loop214 _)
  · rw [if_neg h]
    exact R.skip (n := 131) rfl (ifeq_ne st h)


/-- The MP branch (node 150). -/
theorem mp_branch (st : AS V) (hc : Clean st) :
    Rn (.node 150) st (if wim st.tw st.p1 = st.p2
      then { st with tw := st.p1, ws := cantor 0 st.ws, p2 := 0 }
      else { st with tw := 0, p2 := 0 }) := by
  have := R.seq (n := 150) rfl (R.seq (n := 161) rfl (par1 st hc) (cons _ hc))
    (R.seq (n := 151) rfl (loop216 _) (ifeq_par1 _ hc.2))
  apply rn_eq this
  obtain ⟨h1, h2⟩ := hc
  cases st; simp only at h1 h2; subst h1; subst h2
  simp only [first_cantor, second_cantor, zero_add]

/-- The NIP branch (node 152) when the cache is not the falsity code. -/
theorem nip_branch (st : AS V) (hc : Clean st) (hh : st.p2 ≠ 1) :
    Rn (.node 152) st { st with p2 := first st.ws, ws := second st.ws } := by
  have hinc := inc_AS 6 (by omega) st
  have hne : (updAS st 6 (field st 6 + 1)).s1 ≠ (updAS st 6 (field st 6 + 1)).p2 := by
    show st.s1 + 1 ≠ st.p2
    rw [hc.1, zero_add]
    exact fun h => hh h.symm
  have h132 := R.skip (n := 132) rfl (ifeq_ne _ hne)
  have h153 := R.seq (n := 153) rfl h132 (pop_p2 _ ⟨rfl, hc.2⟩)
  have := R.seq (n := 152) rfl hinc h153
  apply rn_eq this
  obtain ⟨h1, h2⟩ := hc
  cases st; simp only at h1 h2; subst h1; subst h2; simp [updAS, field]

/-- The NIP branch halts on the falsity code. -/
theorem nip_halt (st : AS V) (hc : Clean st) (hh : st.p2 = 1) :
    ∃ y, IR (.node 152) (enc st) .halt y := by
  have hinc := inc_AS 6 (by omega) st
  have heq : (updAS st 6 (field st 6 + 1)).s1 = (updAS st 6 (field st 6 + 1)).p2 := by
    show st.s1 + 1 = st.p2
    rw [hc.1, zero_add, hh]
  have h132 := H.halt_cdr (n := 132) rfl (ifeq_eq _ heq) (H.halt _)
  have h153 := H.halt_car (n := 153) rfl h132
  exact ⟨_, H.halt_cdr (n := 152) rfl hinc h153⟩

theorem loop192 (st : AS V) :
    Rn (.node 192) st {st with s1:=st.s1+st.ac,s2:=st.s2+st.ac,ac:=0} := by
  have h := ArithmeticDagLoops.dagPerm_copy192 R.run_zero R.run_add R.run_one
    ArithmeticDagControlPerm222.spec (enc st)
  rw [lreg_enc _ 6 (by omega),lreg_enc _ 3 (by omega),lreg_enc _ 7 (by omega),
    lupd_enc _ 6 (by omega),lupd_enc _ 7 (by omega),lupd_enc _ 3 (by omega)] at h
  exact h

theorem loop197 (st : AS V) : Rn (.node 197) st {st with p2:=st.p2+st.p1,p1:=0} := by
  have h := ArithmeticDagLoops.transfer (p:=DagPerm.dagPerm) R.run_zero R.run_add R.run_one
    ArithmeticDagControlPerm222.spec (n:=197) (m:=191) (src:=4) (dst:=5)
    rfl rfl (by decide) (enc st)
  rw [lreg_enc _ 5 (by omega),lreg_enc _ 4 (by omega),
    lupd_enc _ 5 (by omega),lupd_enc _ 4 (by omega)] at h
  exact h

/-- Push `x`, saving the current formula. -/
noncomputable def pushA (x : V) (st : AS V) : AS V := { st with tw := x, ws := cantor st.tw st.ws }

/-- Pop a formula and combine it with the current one. -/
noncomputable def popA (op : V → V → V) (st : AS V) : AS V :=
  { st with tw := op (first st.ws) st.tw, ws := second st.ws }

/-- The gate: clear the bundle when `c = b` or `c = a`, and clear `axiomcode`, `param1`,
`param2`. -/
noncomputable def gateF (st : AS V) : AS V :=
  { st with ac := 0, p1 := 0, p2 := 0, tw := if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else st.tw }

theorem l457 (st : AS V) (hc : Clean st) : Rn (.node 457) st (gateF st) := by
  have := R.seq (n := 457) rfl (loop192 st) (R.seq (n := 458) rfl (ifeq_clear _)
    (R.seq (n := 459) rfl (loop211 _) (R.seq (n := 460) rfl (loop197 _) (ifeq_clear _))))
  apply rn_eq this
  obtain ⟨h1, h2⟩ := hc
  cases st
  simp only at h1 h2
  subst h1; subst h2
  simp only [gateF, zero_add]
  split <;> split <;> simp_all 

/-- The register macros of the AX word. -/
inductive AXAtom where
  | par1 | par2 | par3 | push | cons | wel | wal | weq | wn | wa | wex | readp2 | readp1

def AXAtom.node : AXAtom → Nat
  | .par1 => 166 | .par2 => 121 | .par3 => 168 | .push => 171 | .cons => 119 | .wel => 181
  | .wal => 180 | .weq => 182 | .wn => 218 | .wa => 178 | .wex => 183 | .readp2 => 176
  | .readp1 => 175

noncomputable def AXAtom.effect : AXAtom → AS V → AS V
  | .par1, st => pushA st.p1 st
  | .par2, st => pushA st.p2 st
  | .par3, st => pushA st.ac st
  | .push, st => pushA 0 st
  | .cons, st => popA wim st
  | .wel, st => popA ArithmeticCode254.wel st
  | .wal, st => popA ArithmeticCode254.wal st
  | .weq, st => popA ArithmeticCode254.weq st
  | .wa, st => popA ArithmeticDagMacrosPerm222.wa st
  | .wex, st => popA ArithmeticDagMacrosPerm222.wex st
  | .wn, st => { st with tw := ArithmeticDagMacrosPerm222.wn st.tw }
  | .readp2, st => { st with pl := second st.pl, p2 := st.p2 + first st.pl }
  | .readp1, st => { st with pl := second st.pl, p1 := st.p1 + first st.pl }

theorem AXAtom.run (st : AS V) (hc : Clean st) : ∀ a : AXAtom, Rn (.node a.node) st (a.effect st)
  | .par1 => ArithmeticDagMacrosPerm222.par1 st hc
  | .par2 => ArithmeticDagMacrosPerm222.par2 st hc
  | .par3 => ArithmeticDagMacrosPerm222.par3 st hc
  | .push => pushwff st hc
  | .cons => ArithmeticDagMacrosPerm222.cons st hc
  | .wel => wel_m st hc
  | .wal => wal_m st hc
  | .weq => weq_m st hc
  | .wn => wn_m st hc
  | .wa => wa_m st hc
  | .wex => wex_m st hc
  | .readp2 => read_p2 st hc
  | .readp1 => read_p1 st hc

/-- The literal program supplies successors; the certificate names only semantic macros. -/
def axWordCheck : Nat → List AXAtom → Bool
  | n, [] => decide (n = 457)
  | n, a :: rest =>
    match DagPerm.dagPerm.nodes n with
    | (.node m, .node next) => decide (m = a.node) && axWordCheck next rest
    | _ => false

noncomputable def axWordEval : List AXAtom → AS V → AS V
  | [], st => gateF st
  | a :: rest, st => axWordEval rest (a.effect st)

/-- No macro touches the scratch registers. -/
theorem axWordClean (word : List AXAtom) (st : AS V) (hc : Clean st) :
    Clean (axWordEval word st) := by
  induction word generalizing st with
  | nil => exact hc
  | cons a rest ih => exact ih _ (by cases a <;> exact hc)

theorem axWordRun (word : List AXAtom) {n : Nat}
    (h : axWordCheck n word = true) (st : AS V) (hc : Clean st) :
    Rn (.node n) st (axWordEval word st) := by
  induction word generalizing n st with
  | nil =>
    simp only [axWordCheck, decide_eq_true_eq] at h
    subst n
    exact l457 st hc
  | cons a rest ih =>
    simp only [axWordCheck] at h
    split at h
    · rename_i m next hn
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨hm, hr⟩
      subst m
      exact R.seq hn (AXAtom.run st hc a) (ih hr _ (by cases a <;> exact hc))
    · contradiction

def axWord : List AXAtom := [
  .par1, .par2, .wal, .par3, .par1, .readp2, .cons, .readp1, .par1, .cons, .par1, .par3,
  .cons, .par2, .par3, .cons, .cons, .cons, .par3, .par1, .weq, .par3, .par2, .weq,
  .par1, .par2, .wel, .par1, .par2, .weq, .wal, .cons, .cons, .par1, .par1, .par3,
  .wal, .wex, .par3, .cons, .par3, .par1, .weq, .par3, .par2, .wel, .par1, .par2,
  .wel, .cons, .cons, .par1, .par2, .par3, .wal, .wal, .par2, .par1, .par3, .wal,
  .wal, .cons, .par1, .par2, .weq, .par3, .par1, .wel, .par3, .par2, .wel, .cons,
  .cons, .par1, .par2, .par3, .cons, .wal, .par1, .par2, .wal, .par1, .par3, .wal,
  .cons, .cons, .par1, .par1, .par2, .weq, .wex, .par1, .par2, .wel, .par3, .par1,
  .par2, .wel, .wal, .cons, .par3, .par2, .par2, .par3, .wel, .par1, .par3, .par1,
  .par3, .par3, .par1, .wel, .par3, .par2, .wel, .cons, .wal, .par2, .par3, .par2,
  .par3, .par2, .par3, .wel, .wn, .cons, .wal, .wn, .cons, .wal, .cons, .wal,
  .wn, .cons, .wal, .wn, .cons, .wal, .par2, .par3, .par2, .par3, .par2, .par3,
  .wel, .wn, .cons, .wal, .wn, .cons, .wal, .wn, .cons, .wal, .cons, .wn]

theorem axWord_checked : axWordCheck 236 axWord = true := by decide +kernel

noncomputable def f236 (st : AS V) : AS V := axWordEval axWord st
theorem l236 (st : AS V) (hc : Clean st) : Rn (.node 236) st (f236 st) :=
  axWordRun axWord axWord_checked st hc
theorem c236 (st : AS V) (hc : Clean st) : Clean (f236 st) := axWordClean axWord st hc

/-- **The AX routine is EnumPerm's AX step.** -/
theorem ax_eval (np t S c a h pl : V) :
    f236 ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, gateValue (a + first (second pl)) (h + first pl) c,
        axStackValue (a + first (second pl)) h (h + first pl) c a
          t S,
        0, 0, 0, 0, 0, second (second pl)⟩ := by
  simp only [f236, axWord, axWordEval, AXAtom.effect, pushA, popA, gateF,
    first_cantor, second_cantor]
  rfl

/-- The AX leaf (node 149) runs `axioms ()` and breaks out of the dispatch. -/
theorem ax_leaf (st : AS V) (hc : Clean st) :
    IR (.node 149) (enc st) (.brk 1) (enc (f236 st)) :=
  R.brk_cdr (n := 149) (k := 0) rfl (l236 st hc) (R.brkS 0 _)

/-- MP's result on a register file whose parameter already holds `d + x`. -/
noncomputable def mpOut (st : AS V) : AS V :=
  if wim st.tw st.p1 = st.p2 then { st with tw := st.p1, ws := cantor 0 st.ws, p2 := 0 }
  else { st with tw := 0, p2 := 0 }

/-- MP (node 484): read the field into the parameter, then the old MP body. -/
theorem mp484 (st : AS V) (hc : Clean st) :
    Rn (.node 484) st
      (mpOut { st with pl := second st.pl, p1 := st.p1 + first st.pl }) :=
  R.seq (n := 484) rfl (read_p1 st hc) (mp_branch _ hc)

theorem dispatch_nip (st : AS V) (hc : Clean st) (h0 : st.ac = 0) (hh : st.p2 ≠ 1) :
    Rn (.node 141) st { st with p2 := first st.ws, ws := second st.ws } :=
  R.seq (n := 141) rfl (R.skip (n := 142) rfl (decZero_AS 3 (by omega) st h0))
    (nip_branch st hc hh)

theorem dispatch_nip_halt (st : AS V) (hc : Clean st) (h0 : st.ac = 0) (hh : st.p2 = 1) :
    ∃ R', IR (.node 141) (enc st) .halt R' := by
  obtain ⟨R', hR'⟩ := nip_halt st hc hh
  exact ⟨R', H.halt_cdr (n := 141) rfl
    (R.skip (n := 142) rfl (decZero_AS 3 (by omega) st h0)) hR'⟩

/-! The selector levels 142, 145, 148: a level `a = (DEC ac, b)` decrements; with `b = (c, BREAK)`
and `c = (a', body)`, the next level `a'` either dispatches and breaks out (`pass`) or falls
through at `ac = 0` to the body (`fall`); either way `b` then breaks out of the level. -/

theorem dec_brk {a b : Nat} (ha : DagPerm.dagPerm.nodes a = (.decnz 3, .node b)) {st : AS V} (k : V)
    (hk : st.ac = k + 1) {out : V} (hb : IR (.node b) (enc { st with ac := k }) (.brk 1) out) :
    IR (.node a) (enc st) (.brk 1) out := by
  have hdec := decPos_AS 3 (by omega) st k hk
  exact R.brk_cdr (k := 0) ha hdec hb

theorem pass {b c a' : Nat} {e : Edge} (hb : DagPerm.dagPerm.nodes b = (.node c, .brk 1))
    (hc : DagPerm.dagPerm.nodes c = (.node a', e)) {out out' : V} (h : IR (.node a') out (.brk 1) out') :
    IR (.node b) out (.brk 1) out' :=
  R.brk_cdr (k := 0) hb (R.skip hc h) (R.brkS 0 _)

theorem fall {b c a' x : Nat} {e : Edge} (hb : DagPerm.dagPerm.nodes b = (.node c, .brk 1))
    (hc : DagPerm.dagPerm.nodes c = (.node a', e)) (ha' : DagPerm.dagPerm.nodes a' = (.decnz 3, .node x))
    {st st' : AS V} (h0 : st.ac = 0) (he : IR e (enc st) .normal (enc st')) :
    IR (.node b) (enc st) (.brk 1) (enc st') :=
  R.brk_cdr (k := 0) hb (R.seq hc (R.skip ha' (decZero_AS 3 (by omega) st h0)) he) (R.brkS 0 _)

theorem dispatch_drop (st : AS V) (hc : Clean st) :
    Rn (.node 141) { st with ac := 1 } { st with ac := 0, tw := st.p2, ws := cantor st.tw st.ws } :=
  R.skip rfl (dec_brk rfl 0 (by simp) (fall rfl rfl rfl rfl (par2 { st with ac := 0 } hc)))

theorem dispatch_mp (st : AS V) (hc : Clean st) :
    Rn (.node 141) { st with ac := 2 }
      (mpOut { st with ac := 0, pl := second st.pl, p1 := st.p1 + first st.pl }) :=
  R.skip rfl (dec_brk rfl 1 (by dsimp; ring) (pass rfl rfl (dec_brk rfl 0 (by simp)
    (fall rfl rfl rfl rfl (mp484 { st with ac := 0 } hc)))))

theorem dispatch_ax (st : AS V) (hc : Clean st) (c : V) :
    Rn (.node 141) { st with ac := c + 3 } (f236 { st with ac := c }) :=
  R.skip rfl (dec_brk rfl (c + 2) (by dsimp; ring) (pass rfl rfl (dec_brk rfl (c + 1) (by dsimp; ring)
    (pass rfl rfl (dec_brk rfl c rfl (ax_leaf _ hc))))))

/-- Every live scheduler state has this exact nine-register boundary. -/
def boundary (pl np t S d h : V) : AS V := ⟨np,t,S,0,d,h,0,0,pl⟩

lemma selector_cases (k : V) : k=0 ∨ k=1 ∨ k=2 ∨ ∃c, k=c+3 := by
  by_cases h : k<2
  · rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp h) with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · by_cases h2 : k=2
    · exact Or.inr (Or.inr (Or.inl h2))
    · have hk : 2<k := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm h2)
      have h3 : (3:V)≤k := by simpa only [two_add_one_eq_three] using lt_iff_succ_le.mp hk
      exact Or.inr (Or.inr (Or.inr ⟨k-3,(tsub_add_cancel_of_le h3).symm⟩))

/-- The selector read uses one field; payload consumption belongs to dispatch. -/
theorem read_run (raw np t S d h : V) {X : AS V}
    (hd : Rn (.node 141) ⟨np,t,S,first raw,d,h,0,0,second raw⟩ X) :
    Rn (.node 139) (boundary raw np t S d h) X := by
  have hr := read_ac (boundary raw np t S d h) ⟨rfl,rfl⟩
  simp only [boundary,zero_add] at hr
  exact R.seq (n:=139) rfl hr hd

/-- Actual command execution, including all zero and malformed raw words. -/
theorem command_step (raw np t S d h : V) :
    (stepValue raw (stateValue t S d h)=0 ∧
      ∃y, IR (.node 139) (enc (boundary raw np t S d h)) .halt y) ∨
    ∃t' S' d' h', stepValue raw (stateValue t S d h)=someState t' S' d' h' ∧
      Rn (.node 139) (boundary raw np t S d h)
        (boundary (tailValue raw) np t' S' d' h') := by
  rcases selector_cases (first raw) with h0|h1|h2|⟨c,hc⟩
  · by_cases hh : h=1
    · refine Or.inl ⟨by simp [stepValue,stateValue,effectValue,h0,hh],?_⟩
      obtain ⟨y,hy⟩ := dispatch_nip_halt (⟨np,t,S,first raw,d,h,0,0,second raw⟩ : AS V)
        ⟨rfl,rfl⟩ h0 hh
      have hr := read_ac (boundary raw np t S d h) ⟨rfl,rfl⟩
      simp only [boundary,zero_add] at hr
      exact ⟨y,H.halt_cdr (n:=139) rfl hr hy⟩
    · refine Or.inr ⟨t,second S,d,first S,by simp [stepValue,stateValue,effectValue,h0,hh],?_⟩
      have hd := dispatch_nip (⟨np,t,S,first raw,d,h,0,0,second raw⟩ : AS V)
        ⟨rfl,rfl⟩ h0 hh
      exact rn_eq (read_run raw np t S d h hd) (by simp [boundary,tailValue,h0])
  · refine Or.inr ⟨h,cantor t S,d,h,by simp [stepValue,stateValue,effectValue,h1],?_⟩
    have hd := dispatch_drop (⟨np,t,S,0,d,h,0,0,second raw⟩ : AS V) ⟨rfl,rfl⟩
    have he : (⟨np,t,S,first raw,d,h,0,0,second raw⟩ : AS V)=
        ⟨np,t,S,1,d,h,0,0,second raw⟩ := by rw [h1]
    exact rn_eq (read_run raw np t S d h (he ▸ hd)) (by simp [boundary,tailValue,h1])
  · have hd := dispatch_mp (⟨np,t,S,0,d,h,0,0,second raw⟩ : AS V) ⟨rfl,rfl⟩
    have he : (⟨np,t,S,first raw,d,h,0,0,second raw⟩ : AS V)=
        ⟨np,t,S,2,d,h,0,0,second raw⟩ := by rw [h2]
    have hr := read_run raw np t S d h (he ▸ hd)
    by_cases hm : wim t (d+first (second raw))=h
    · refine Or.inr ⟨d+first (second raw),cantor 0 S,d+first (second raw),0,
        by simp [stepValue,stateValue,effectValue,h2,hm],?_⟩
      simpa only [mpOut,hm,if_true,boundary,tailValue,h2,lt_self_iff_false,if_false] using hr
    · refine Or.inr ⟨0,S,d+first (second raw),0,
        by simp [stepValue,stateValue,effectValue,h2,hm],?_⟩
      simpa only [mpOut,hm,if_false,boundary,tailValue,h2,lt_self_iff_false,if_true] using hr
  · have h3 : (3:V)≤first raw := hc ▸ le_add_self
    have h23 : (2:V)<3 := by simpa only [two_add_one_eq_three] using lt_add_one (2:V)
    have hk := lt_of_lt_of_le h23 h3
    have hz : first raw≠0 := ne_of_gt (lt_trans (by simp : (0:V)<2) hk)
    have ho : first raw≠1 := ne_of_gt (lt_trans (by simp : (1:V)<2) hk)
    have ht : first raw≠2 := ne_of_gt hk
    have hsub : first raw-3=c := by rw [hc,add_tsub_cancel_right]
    refine Or.inr ⟨gateValue (d+first (second (second raw))) (h+first (second raw)) c,
      axStackValue (d+first (second (second raw))) h (h+first (second raw)) c d t S,0,0,
      by simp [stepValue,stateValue,effectValue,hz,ho,ht,hsub],?_⟩
    have hd := dispatch_ax (⟨np,t,S,0,d,h,0,0,second raw⟩ : AS V) ⟨rfl,rfl⟩ c
    have he : (⟨np,t,S,first raw,d,h,0,0,second raw⟩ : AS V)=
        ⟨np,t,S,c+3,d,h,0,0,second raw⟩ := by rw [hc]
    have hr := read_run raw np t S d h (he ▸ hd)
    rw [ax_eval] at hr
    simpa only [boundary,tailValue,not_lt_of_ge (le_of_lt hk),ht,if_false] using hr

/-- Actual fetch, preserving all working registers. -/
theorem fetch_run (pl np t S d h : V) :
    Rn (.node 133) (boundary pl np t S d h)
      (boundary (first (fetchValue pl np)) (second (fetchValue pl np)) t S d h) := by
  by_cases hz : pl=0
  · subst pl
    simpa only [boundary,raw_new,next_new] using fetch_zero (boundary 0 np t S d h) rfl rfl
  · have hp := pred_add_one pl hz
    have hf := fetch_pos (boundary pl np t S d h) (pl-1) hp.symm
    simpa only [boundary,fetchValue,hz,if_false,first_cantor,second_cantor] using hf

/-- One unconditional actual root execution, with scheduler progress. -/
theorem root_step (pl np t S d h : V) :
    (enumValue (DiophantineConsistency.ArithmeticEnumStepPerm222.liveValue pl np (stateValue t S d h))=0 ∧
      ∃y, IR (.node 0) (enc (boundary pl np t S d h)) .halt y) ∨
    ∃pl' np' t' S' d' h',
      enumValue (DiophantineConsistency.ArithmeticEnumStepPerm222.liveValue pl np (stateValue t S d h))=
        DiophantineConsistency.ArithmeticEnumStepPerm222.liveValue pl' np' (stateValue t' S' d' h') ∧
      Rn (.node 0) (boundary pl np t S d h) (boundary pl' np' t' S' d' h') ∧
      (pl'<pl ∨ np'=np+1) := by
  have hf := fetch_run pl np t S d h
  rcases command_step (first (fetchValue pl np)) (second (fetchValue pl np)) t S d h with
    ⟨hz,y,hy⟩|⟨t',S',d',h',he,hr⟩
  · refine Or.inl ⟨?_,y,H.halt_cdr (n:=0) rfl hf hy⟩
    rw [enum_live,execValue, hz,if_pos rfl]
  · refine Or.inr ⟨tailValue (first (fetchValue pl np)),second (fetchValue pl np),t',S',d',h',?_,
      R.seq (n:=0) rfl hf hr,?_⟩
    · rw [enum_live,execValue,he]
      simp [someState]
    · by_cases hz : pl=0
      · right;subst pl;exact next_new np
      · left;exact lt_iff_succ_le.mpr (continuation_progress pl np hz)

end SetTheory.BusyBeaver.ZFC.ArithmeticDagRootPerm222
