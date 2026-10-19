import BusyBeaver.ZFC.ArithmeticL2AxiomsEval254
import BusyBeaver.ZFC.ArithmeticEnumeratorStep254

set_option autoImplicit false

/-!
# Internal L2, part 6: one root run is one arithmetic scheduler step

The internal counterpart of `L2Root254`, in every model of `IΣ₁`. `ax_eval`
identifies the evaluated `axioms()` composite with the AX effect of the
represented command step `ArithmeticCommandStep254.effectValue` (the gated
bundle `gateValue` and the stack `axStackValue`, built from the circuits of
`ArithmeticTemplates254`). The dispatch, fetch and read lemmas then give
`root_step`: from the record of a live scheduler configuration, the structured
run of the root (node 0) either halts, when the scheduler step is the absorbing
zero, or exits normally at the record of the next configuration.
-/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticL2

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticDagRun RMDag
open ArithmeticCode254 (wim wel wal weq tagged rho1)
open ArithmeticTemplates254 (Circuit bundle bundleCircuit rho2 rho2Circuit rho3 rho3Circuit
  rho4 rho4Circuit rho5 rho5Circuit rho6 rho6Circuit rho7 rho7Circuit rho8 rho8Circuit)

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ax_eval (np t S c a h pl : V) :
    f1 ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, ArithmeticCommandStep254.gateValue a (h + first pl) c,
        ArithmeticCommandStep254.axStackValue a h (h + first pl) c (first (second pl)) t S,
        0, 0, 0, 0, 0, second (second pl)⟩ := by
  rw [e1]
  simp only [ArithmeticCommandStep254.gateValue, ArithmeticCommandStep254.axStackValue,
    bundle, bundleCircuit, Circuit.bundle, Circuit.container, Circuit.collection, Circuit.conj,
    Circuit.ex, Circuit.neg, Circuit.eval_im, Circuit.eval_el, Circuit.eval_al, Circuit.eval_eq,
    Circuit.eval_input0, Circuit.eval_input1, Circuit.eval_input2, Circuit.eval_input3,
    Circuit.eval_one, rho1, rho2, rho2Circuit, rho3, rho3Circuit, rho4, rho4Circuit, rho5,
    rho5Circuit, rho6, rho6Circuit, rho7, rho7Circuit, rho8, rho8Circuit, Circuit.r2, Circuit.r3,
    Circuit.r4, Circuit.r5, Circuit.r6, Circuit.r7, Circuit.r8, wn, wa, wex]

/-! ## The dispatch -/

theorem ax_leaf (st : AS V) (hc : Clean st) : IR (.node 149) (enc st) (.brk 1) (enc (f1 st)) :=
  R.brk_cdr (n := 149) (k := 0) rfl (l1 st hc) (R.brkS 0 _)

theorem dispatch_mp (st : AS V) (hc : Clean st) (h0 : st.ac = 0) :
    Rn (.node 141) st (if wim st.tw st.p1 = st.p2
      then { st with tw := st.p1, ws := cantor 0 st.ws, p2 := 0 } else { st with tw := 0, p2 := 0 }) :=
  R.seq (n := 141) rfl (R.skip (n := 142) rfl (decZero_AS 3 (by omega) st h0)) (mp_branch st hc)

theorem dispatch_drop (st : AS V) (hc : Clean st) :
    Rn (.node 141) { st with ac := 1 } { st with ac := 0, tw := st.p2, ws := cantor st.tw st.ws } := by
  have hdec := decPos_AS 3 (by omega) { st with ac := 1 } 0 (by simp [field])
  let st0 : AS V := { st with ac := 0 }
  have h145 : Rn (.node 145) st0 st0 := R.skip (n := 145) rfl (decZero_AS 3 (by omega) st0 rfl)
  have h144 := R.seq (n := 144) rfl h145 (par2 st0 hc)
  have h143 := R.brk_cdr (n := 143) (k := 0) rfl h144 (R.brkS 0 _)
  have h142 := R.brk_cdr (n := 142) (k := 0) rfl hdec h143
  exact R.skip (n := 141) rfl h142

theorem dispatch_nip (st : AS V) (hc : Clean st) (hh : st.p2 ≠ 1) :
    Rn (.node 141) { st with ac := 2 }
      { st with ac := 0, p2 := first st.ws, ws := second st.ws } := by
  have hdec1 := decPos_AS 3 (by omega) { st with ac := 2 } 1 (by simp [field]; norm_num)
  have hdec2 := decPos_AS 3 (by omega) { st with ac := 1 } 0 (by simp [field])
  let st0 : AS V := { st with ac := 0 }
  have h148 : Rn (.node 148) st0 st0 := R.skip (n := 148) rfl (decZero_AS 3 (by omega) st0 rfl)
  have h147 := R.seq (n := 147) rfl h148 (nip_branch st0 hc hh)
  have h146 := R.brk_cdr (n := 146) (k := 0) rfl h147 (R.brkS 0 _)
  have h145 := R.brk_cdr (n := 145) (k := 0) rfl hdec2 h146
  have h144 := R.skip (n := 144) rfl h145
  have h143 := R.brk_cdr (n := 143) (k := 0) rfl h144 (R.brkS 0 _)
  have h142 := R.brk_cdr (n := 142) (k := 0) rfl hdec1 h143
  exact R.skip (n := 141) rfl h142

theorem dispatch_nip_halt (st : AS V) (hc : Clean st) (hh : st.p2 = 1) :
    ∃ y, IR (.node 141) (enc { st with ac := 2 }) .halt y := by
  have hdec1 := decPos_AS 3 (by omega) { st with ac := 2 } 1 (by simp [field]; norm_num)
  have hdec2 := decPos_AS 3 (by omega) { st with ac := 1 } 0 (by simp [field])
  let st0 : AS V := { st with ac := 0 }
  obtain ⟨y, hy⟩ := nip_halt st0 hc hh
  have h148 : Rn (.node 148) st0 st0 := R.skip (n := 148) rfl (decZero_AS 3 (by omega) st0 rfl)
  have h147 := R.halt_cdr (n := 147) rfl h148 hy
  have h146 := R.halt_car (n := 146) rfl h147
  have h145 := R.halt_cdr (n := 145) rfl hdec2 h146
  have h144 := R.halt_car (n := 144) rfl h145
  have h143 := R.halt_car (n := 143) rfl h144
  have h142 := R.halt_cdr (n := 142) rfl hdec1 h143
  exact ⟨y, R.halt_car (n := 141) rfl h142⟩

theorem dispatch_ax (st : AS V) (hc : Clean st) (c : V) :
    Rn (.node 141) { st with ac := c + 3 } (f1 { st with ac := c }) := by
  have hdec1 := decPos_AS 3 (by omega) { st with ac := c + 3 } (c + 2) (by
    show c + 3 = c + 2 + 1; rw [add_assoc]; norm_num)
  have hdec2 := decPos_AS 3 (by omega) { st with ac := c + 2 } (c + 1) (by
    show c + 2 = c + 1 + 1; rw [add_assoc]; norm_num)
  have hdec3 := decPos_AS 3 (by omega) { st with ac := c + 1 } c rfl
  have h148 := R.brk_cdr (n := 148) (k := 0) rfl hdec3 (ax_leaf { st with ac := c } hc)
  have h147 := R.skip (n := 147) rfl h148
  have h146 := R.brk_cdr (n := 146) (k := 0) rfl h147 (R.brkS 0 _)
  have h145 := R.brk_cdr (n := 145) (k := 0) rfl hdec2 h146
  have h144 := R.skip (n := 144) rfl h145
  have h143 := R.brk_cdr (n := 143) (k := 0) rfl h144 (R.brkS 0 _)
  have h142 := R.brk_cdr (n := 142) (k := 0) rfl hdec1 h143
  exact R.skip (n := 141) rfl h142

/-! ## Fetch and reads -/

/-- Scheduler configurations as boundary records. -/
def toAS (pl np t s d h : V) : AS V := ⟨np, t, s, 0, d, h, 0, 0, pl⟩

theorem fetch_run_pos (pl np t s d h : V) (hp : pl ≠ 0) :
    Rn (.node 133) (toAS pl np t s d h) (toAS (pl - 1) np t s d h) := by
  have hv : pl = (pl - 1) + 1 :=
    (tsub_add_cancel_of_le (one_le_of_pos (lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm hp)))).symm
  exact fetch_pos (toAS pl np t s d h) (pl - 1) hv

theorem fetch_run_zero (np t s d h : V) :
    Rn (.node 133) (toAS 0 np t s d h) (toAS np (np + 1) t s d h) :=
  fetch_zero (toAS 0 np t s d h) rfl rfl

/-- The two reads after the fetch. -/
theorem reads_run (np pl1 tw ws d h : V) {X : AS V}
    (hd : Rn (.node 141) ⟨np, tw, ws, first pl1, d + first (second pl1), h, 0, 0,
      second (second pl1)⟩ X) :
    Rn (.node 139) ⟨np, tw, ws, 0, d, h, 0, 0, pl1⟩ X := by
  have h174 := read_ac ⟨np, tw, ws, 0, d, h, 0, 0, pl1⟩ ⟨rfl, rfl⟩
  have h175 := read_p1 { (⟨np, tw, ws, 0, d, h, 0, 0, pl1⟩ : AS V) with
    pl := second pl1, ac := 0 + first pl1 } ⟨rfl, rfl⟩
  simp only [zero_add] at h174 h175
  exact R.seq (n := 139) rfl h174 (R.seq (n := 140) rfl h175 hd)

end SetTheory.BusyBeaver.ZFC.ArithmeticL2
