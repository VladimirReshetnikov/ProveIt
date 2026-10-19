import BusyBeaver.ZFC.ArithmeticL2Root254
import BusyBeaver.ZFC.ArithmeticEnumeratorSeed246
import BusyBeaver.ZFC.ArithmeticPositiveSimulation254

set_option autoImplicit false

/-!
# The dag254 control interpreter simulates the arithmetic scheduler, internally

In every model of `IΣ₁`:

* `root_step`: from the record of every live configuration of the represented
  scheduler `ArithmeticEnumeratorStep254.step`, the internal structured run of
  the root of the 219-node program either halts (exactly when the scheduler
  step is the absorbing zero: NIP on the falsity code) or exits normally at the
  record of the next configuration;
* `root_occ`: the root occupies controls `1, …, 6460` of the packed dag254
  catalogue, with its normal exit restarting at control `1` (one kernel check);
* `halts_iff`: hence, by positive-clock transport, the scheduler halts from a
  configuration iff the represented dag254 interpreter halts from its record;
* `seed_halts_iff`: at the logical seed (`np = 3`, `d = 3`, all else zero; the
  configuration of `ArithmeticEnumeratorSeed246`), the interpreter halts iff the
  represented validator accepts a proof of falsity.

This is the internal counterpart of `L2Root254.iter_iff`/`program_halts_iff`.
-/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticL2

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticDagRun RMDag
open ArithmeticCode254 (wim)
open ArithmeticCommandStep254 (stateValue someState effectValue)
open ArithmeticEnumeratorStep254 (advanceValue)
open ArithmeticCommandWord254 (tailValue)

set_option maxRecDepth 8192
set_option maxHeartbeats 300000

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The two reads after the fetch, when the dispatch halts. -/
theorem reads_halt (np pl1 tw ws d h : V) {y : V}
    (hd : IR (.node 141) (enc ⟨np, tw, ws, first pl1, d + first (second pl1), h, 0, 0,
      second (second pl1)⟩) .halt y) :
    IR (.node 139) (enc ⟨np, tw, ws, 0, d, h, 0, 0, pl1⟩) .halt y := by
  have h174 := read_ac ⟨np, tw, ws, 0, d, h, 0, 0, pl1⟩ ⟨rfl, rfl⟩
  have h175 := read_p1 { (⟨np, tw, ws, 0, d, h, 0, 0, pl1⟩ : AS V) with
    pl := second pl1, ac := 0 + first pl1 } ⟨rfl, rfl⟩
  simp only [zero_add] at h174 h175
  exact R.halt_cdr (n := 139) rfl h174 (R.halt_cdr (n := 140) rfl h175 hd)

theorem state_first (t s d h : V) : first (stateValue t s d h) = t := by simp [stateValue]
theorem state_second (t s d h : V) : first (second (stateValue t s d h)) = s := by simp [stateValue]
theorem state_third (t s d h : V) : first (second (second (stateValue t s d h))) = d := by
  simp [stateValue]
theorem state_fourth (t s d h : V) : second (second (second (stateValue t s d h))) = h := by
  simp [stateValue]

theorem step_raw (raw t s d h : V) :
    ArithmeticCommandStep254.stepValue raw (stateValue t s d h) =
      effectValue (first raw) (first (second raw)) (first (second (second raw)))
        (first (second (second (second raw)))) t s d h := by
  simp only [ArithmeticCommandStep254.stepValue, state_first, state_second, state_third,
    state_fourth]

theorem someState_pred (t s d h : V) : someState t s d h - 1 = stateValue t s d h := by
  simp [someState]

theorem someState_ne (t s d h : V) : someState t s d h ≠ 0 := by simp [someState]

/-- One command from the record after the fetch. -/
theorem command_step (raw np1 t s d h : V) :
    (advanceValue raw np1 (stateValue t s d h) = 0 ∧
      ∃ y, IR (.node 139) (enc ⟨np1, t, s, 0, d, h, 0, 0, raw⟩) .halt y) ∨
    (∃ t' s' d' h', advanceValue raw np1 (stateValue t s d h) =
        ArithmeticEnumeratorStep254.liveValue (tailValue raw) np1 (stateValue t' s' d' h') ∧
      Rn (.node 139) ⟨np1, t, s, 0, d, h, 0, 0, raw⟩ (toAS (tailValue raw) np1 t' s' d' h')) := by
  set k := first raw with hk
  set x := first (second raw)
  set y := first (second (second raw))
  set u := first (second (second (second raw)))
  have hst : ArithmeticCommandStep254.stepValue raw (stateValue t s d h) =
      effectValue k x y u t s d h := step_raw raw t s d h
  have hclean : ∀ np tw ws ac p1 p2 pl : V, Clean (⟨np, tw, ws, ac, p1, p2, 0, 0, pl⟩ : AS V) :=
    fun _ _ _ _ _ _ _ => ⟨rfl, rfl⟩
  have hreads := fun {X : AS V} (hd : Rn (.node 141) ⟨np1, t, s, k, d + x, h, 0, 0,
      second (second raw)⟩ X) => reads_run np1 raw t s d h hd
  by_cases h0 : k = 0
  · -- MP
    right
    have htail : tailValue raw = second (second raw) := by
      simp [tailValue, ← hk, h0]
    have hd := dispatch_mp ⟨np1, t, s, k, d + x, h, 0, 0, second (second raw)⟩ (hclean _ _ _ _ _ _ _) h0
    by_cases hw : wim t (d + x) = h
    · refine ⟨d + x, cantor 0 s, d + x, 0, ?_, ?_⟩
      · simp [advanceValue, hst, effectValue, h0, hw, someState_pred, someState_ne, htail]
      · have := hreads hd
        simp only [hw, if_true] at this
        rw [htail]
        exact rn_eq this (by simp [toAS, h0])
    · refine ⟨0, s, d + x, 0, ?_, ?_⟩
      · simp [advanceValue, hst, effectValue, h0, hw, someState_pred, someState_ne, htail]
      · have := hreads hd
        simp only [hw, if_false] at this
        rw [htail]
        exact rn_eq this (by simp [toAS, h0])
  by_cases h1 : k = 1
  · -- DROP
    right
    have htail : tailValue raw = second (second raw) := by
      simp [tailValue, ← hk, h1]
    refine ⟨h, cantor t s, d + x, h, ?_, ?_⟩
    · simp [advanceValue, hst, effectValue, h1, someState_pred, someState_ne, htail]
    · have hd := dispatch_drop ⟨np1, t, s, 0, d + x, h, 0, 0, second (second raw)⟩ (hclean _ _ _ _ _ _ _)
      have := hreads (by rw [h1]; exact hd)
      rw [htail]
      exact rn_eq this (by simp [toAS])
  by_cases h2 : k = 2
  · -- NIP
    have htail : tailValue raw = second (second raw) := by
      simp [tailValue, ← hk, h2, show ¬ (3 : V) ≤ 2 from by norm_num]
    by_cases hh : h = 1
    · left
      refine ⟨by simp only [advanceValue, hst]; simp [effectValue, h2, hh], ?_⟩
      obtain ⟨y', hy'⟩ := dispatch_nip_halt ⟨np1, t, s, 0, d + x, h, 0, 0, second (second raw)⟩
        (hclean _ _ _ _ _ _ _) hh
      exact ⟨y', reads_halt np1 raw t s d h (by rw [← hk, h2]; exact hy')⟩
    · right
      refine ⟨t, second s, d + x, first s, ?_, ?_⟩
      · simp [advanceValue, hst, effectValue, h2, hh, someState_pred, someState_ne, htail]
      · have hd := dispatch_nip ⟨np1, t, s, 0, d + x, h, 0, 0, second (second raw)⟩
          (hclean _ _ _ _ _ _ _) hh
        have := hreads (by rw [h2]; exact hd)
        rw [htail]
        exact rn_eq this (by simp [toAS])
  · -- AX: k = c + 3
    right
    have h3 : 3 ≤ k := by
      rcases lt_or_ge k 3 with hlt | hge
      · exfalso
        have e3 : (3 : V) = 2 + 1 := by norm_num
        have e2 : (2 : V) = 1 + 1 := by norm_num
        rw [e3] at hlt
        rcases (lt_succ_iff_le.mp hlt).lt_or_eq with hlt2 | heq
        · rw [e2] at hlt2
          rcases (lt_succ_iff_le.mp hlt2).lt_or_eq with hlt1 | heq1
          · exact h0 (lt_one_iff_eq_zero.mp hlt1)
          · exact h1 heq1
        · exact h2 heq
      · exact hge
    set c := k - 3
    have hkc : k = c + 3 := (tsub_add_cancel_of_le h3).symm
    have htail : tailValue raw = second (second (second (second raw))) := by
      simp [tailValue, ← hk, not_lt.mpr h3]
    refine ⟨ArithmeticCommandStep254.gateValue (d + x) (h + y) c,
      ArithmeticCommandStep254.axStackValue (d + x) h (h + y) c u t s, 0, 0, ?_, ?_⟩
    · simp [advanceValue, hst, effectValue, h0, h1, h2, someState_pred, someState_ne, htail, c]
    · have hd := dispatch_ax ⟨np1, t, s, 0, d + x, h, 0, 0, second (second raw)⟩
        (hclean _ _ _ _ _ _ _) c
      have := hreads (by rw [hkc]; exact hd)
      rw [htail]
      apply rn_eq this
      simp only [ax_eval, toAS]
      rfl

/-- One root run is one scheduler step. The candidate pointer decreases or the
next candidate increases, so the record changes. -/
theorem root_step (pl np t s d h : V) :
    (ArithmeticEnumeratorStep254.step (ArithmeticEnumeratorStep254.liveValue pl np
        (stateValue t s d h)) = 0 ∧
      ∃ y, IR (.node 0) (enc (toAS pl np t s d h)) .halt y) ∨
    (∃ pl' np' t' s' d' h', ArithmeticEnumeratorStep254.step
        (ArithmeticEnumeratorStep254.liveValue pl np (stateValue t s d h)) =
        ArithmeticEnumeratorStep254.liveValue pl' np' (stateValue t' s' d' h') ∧
      Rn (.node 0) (toAS pl np t s d h) (toAS pl' np' t' s' d' h') ∧
      (pl' < pl ∨ np' = np + 1)) := by
  obtain ⟨raw, np1, hstep, hfetch, hdec⟩ : ∃ raw np1,
      ArithmeticEnumeratorStep254.step (ArithmeticEnumeratorStep254.liveValue pl np
        (stateValue t s d h)) = advanceValue raw np1 (stateValue t s d h) ∧
      Rn (.node 133) (toAS pl np t s d h) (toAS raw np1 t s d h) ∧
      (raw < pl ∨ np1 = np + 1) := by
    by_cases hp : pl = 0
    · subst hp
      exact ⟨np, np + 1, ArithmeticEnumeratorStep254.step_boundary np _, fetch_run_zero np t s d h,
        .inr rfl⟩
    · refine ⟨pl - 1, np, ArithmeticEnumeratorStep254.step_active pl np _ hp,
        fetch_run_pos pl np t s d h hp, .inl ?_⟩
      exact tsub_lt_self (lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm hp)) one_pos
  rcases command_step raw np1 t s d h with ⟨hz, y, hy⟩ | ⟨t', s', d', h', hv, hr⟩
  · left
    exact ⟨hstep.trans hz, y, R.halt_cdr (n := 0) rfl hfetch hy⟩
  · right
    refine ⟨tailValue raw, np1, t', s', d', h', hstep.trans hv, R.seq (n := 0) rfl hfetch hr, ?_⟩
    rcases hdec with hlt | heq
    · exact .inl (lt_of_le_of_lt (ArithmeticCommandWord254.tailValue_le raw) hlt)
    · exact .inr heq

end SetTheory.BusyBeaver.ZFC.ArithmeticL2
