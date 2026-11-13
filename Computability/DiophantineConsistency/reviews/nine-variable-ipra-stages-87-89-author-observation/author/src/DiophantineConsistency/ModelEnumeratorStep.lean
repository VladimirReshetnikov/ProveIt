import DiophantineConsistency.ModelEnumeratorRows
import DiophantineConsistency.ArithmeticEnumStepPerm222

/-! # One step of the enumerator program against the internal C222 machine

The program `DirectEnumerator.optionStepProgram` acts on option-state codes:
`0` is `none`, and `encV pl np tw ws d h + 1` (six Foundation-paired
registers) is a live state. The internal machine
`ArithmeticEnumStepPerm222.enumValue` acts on Cantor codes: `0` is halted,
and `liveValue pl np (stateValue tw ws d h)` is a live state. `StateRel x m`
says that the program code `x` and the machine code `m` denote the same
state.

`rel_optionStep`: one program step and one machine step preserve `StateRel`,
in every model `V` of `𝗜𝚺₁` and at all (possibly nonstandard) registers. The
proof follows the literal branch structure of `DirectEnumerator.rawStep`
(tags `0`, `1`, `2`, `≥ 3`) against `effectValue`, `tailValue` and
`fetchValue` of the machine; every branch of the program is selected with
`if_pos`/`if_neg` on an explicitly evaluated condition, so no decidability
instance is ever compared. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelEnumeratorStep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelScalarPR ScalarPRCode DirectScalar ModelDirectScalar ModelEnumeratorCantor
  ModelEnumeratorRows
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open ArithmeticCommandWordPerm222 ArithmeticCommandFetchPerm222 ArithmeticCommandStepPerm222
  ArithmeticEnumStepPerm222

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Program and machine codes of the same enumerator state. -/
def StateRel (x m : V) : Prop :=
  (x = 0 ∧ m = 0) ∨
    ∃ pl np tw ws d h : V, x = encV pl np tw ws d h + 1 ∧ m = liveValue pl np (stateValue tw ws d h)

/-! ### Elementary facts in the model -/

theorem succ_ne_zero' (x : V) : x + 1 ≠ 0 :=
  (lt_of_le_of_lt (LO.FirstOrder.Arithmetic.zero_le x)
    (LO.FirstOrder.Arithmetic.lt_succ_iff_le.mpr le_rfl)).ne'

theorem liveValue_ne_zero (a b c : V) : liveValue a b c ≠ 0 := by
  unfold liveValue
  exact succ_ne_zero' _

theorem eq_zero_or_one_of_lt_two {k : V} (hk : k < 2) : k = 0 ∨ k = 1 := by
  have h1 : k ≤ 1 := LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp (by rwa [one_add_one_eq_two])
  rcases lt_or_eq_of_le h1 with hlt | heq
  · left
    have h0 : k ≤ 0 := LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp (by rwa [zero_add])
    exact le_antisymm h0 (LO.FirstOrder.Arithmetic.zero_le k)
  · exact Or.inr heq

/-! ### The machine, case by case -/

section Machine
variable {raw k p q t s d h z np w : V}

theorem stepValue_state (raw t s d h : V) :
    stepValue raw (stateValue t s d h) =
      effectValue (first raw) (first (second raw)) (first (second (second raw))) t s d h := by
  simp only [stepValue, stateValue, first_cantor, second_cantor]

theorem effect_k0_halt (hk : k = 0) (hh : h = 1) : effectValue k p q t s d h = 0 := by
  rw [effectValue, if_pos hk, if_pos hh]

theorem effect_k0_live (hk : k = 0) (hh : h ≠ 1) :
    effectValue k p q t s d h = someState t (second s) d (first s) := by
  rw [effectValue, if_pos hk, if_neg hh]

theorem effect_k1 (hk : k = 1) : effectValue k p q t s d h = someState h (cantor t s) d h := by
  rw [effectValue, if_neg (show k ≠ 0 by rw [hk]; exact _root_.one_ne_zero), if_pos hk]

theorem effect_k2_mp (hk : k = 2) (hm : wim t (d + p) = h) :
    effectValue k p q t s d h = someState (d + p) (cantor 0 s) (d + p) 0 := by
  rw [effectValue, if_neg (show k ≠ 0 by rw [hk]; exact zero_lt_two.ne'),
    if_neg (show k ≠ 1 by rw [hk]; exact one_lt_two.ne'), if_pos hk, if_pos hm]

theorem effect_k2_skip (hk : k = 2) (hm : ¬ wim t (d + p) = h) :
    effectValue k p q t s d h = someState 0 s (d + p) 0 := by
  rw [effectValue, if_neg (show k ≠ 0 by rw [hk]; exact zero_lt_two.ne'),
    if_neg (show k ≠ 1 by rw [hk]; exact one_lt_two.ne'), if_pos hk, if_neg hm]

theorem effect_k3 (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) :
    effectValue k p q t s d h =
      someState (gateValue (d + q) (h + p) (k - 3)) (axStackValue (d + q) h (h + p) (k - 3) d t s)
        0 0 := by
  rw [effectValue, if_neg h0, if_neg h1, if_neg h2]

theorem tail_lt_two (hk : first z < 2) : tailValue z = second z := by
  rw [tailValue, if_pos hk]

theorem tail_two (hk : first z = 2) : tailValue z = second (second z) := by
  rw [tailValue, if_neg (show ¬ first z < 2 by rw [hk]; exact _root_.lt_irrefl 2), if_pos hk]

theorem tail_three (h0 : first z ≠ 0) (h1 : first z ≠ 1) (h2 : first z ≠ 2) :
    tailValue z = second (second (second z)) := by
  rw [tailValue, if_neg (fun hl => (eq_zero_or_one_of_lt_two hl).elim h0 h1), if_neg h2]

theorem exec_of_step_zero (hs : stepValue raw w = 0) : execValue raw np w = 0 := by
  simp only [execValue]
  rw [hs, if_pos rfl]

theorem exec_of_step (hs : stepValue raw w = someState t s d h) :
    execValue raw np w = liveValue (tailValue raw) np (stateValue t s d h) := by
  simp only [execValue]
  rw [hs, someState, if_neg (succ_ne_zero' _), add_tsub_cancel_right]

end Machine

/-! ### The raw step program -/

theorem rawStepProgram_val {a b : ℕ → ℕ} (ha : R a) (hb : R b) :
    (DirectEnumerator.rawStepProgram ha hb).val =
      (ifEq (DirectEnumerator.unpairLeft ha) (constant 0)
        (ifEq DirectEnumerator.cache (constant 1) Realizes.zero
          (successor (DirectEnumerator.state (DirectEnumerator.unpairRight ha) hb
            DirectEnumerator.tw (DirectEnumerator.unpairRight DirectEnumerator.ws)
            DirectEnumerator.depth (DirectEnumerator.unpairLeft DirectEnumerator.ws))))
        (ifEq (DirectEnumerator.unpairLeft ha) (constant 1)
          (successor (DirectEnumerator.state (DirectEnumerator.unpairRight ha) hb
            DirectEnumerator.cache (DirectEnumerator.cantorPair DirectEnumerator.tw DirectEnumerator.ws)
            DirectEnumerator.depth DirectEnumerator.cache))
          (ifEq (DirectEnumerator.unpairLeft ha) (constant 2)
            (ifEq (DirectEnumerator.implication DirectEnumerator.tw
                (add DirectEnumerator.depth
                  (DirectEnumerator.unpairLeft (DirectEnumerator.unpairRight ha))))
              DirectEnumerator.cache
              (successor (DirectEnumerator.state
                (DirectEnumerator.unpairRight (DirectEnumerator.unpairRight ha)) hb
                (add DirectEnumerator.depth
                  (DirectEnumerator.unpairLeft (DirectEnumerator.unpairRight ha)))
                (DirectEnumerator.cantorPair Realizes.zero DirectEnumerator.ws)
                (add DirectEnumerator.depth
                  (DirectEnumerator.unpairLeft (DirectEnumerator.unpairRight ha)))
                Realizes.zero))
              (successor (DirectEnumerator.state
                (DirectEnumerator.unpairRight (DirectEnumerator.unpairRight ha)) hb
                Realizes.zero DirectEnumerator.ws
                (add DirectEnumerator.depth
                  (DirectEnumerator.unpairLeft (DirectEnumerator.unpairRight ha)))
                Realizes.zero)))
            (successor (DirectEnumerator.state
              (DirectEnumerator.unpairRight
                (DirectEnumerator.unpairRight (DirectEnumerator.unpairRight ha))) hb
              (DirectEnumerator.gated
                (add DirectEnumerator.depth (DirectEnumerator.unpairLeft
                  (DirectEnumerator.unpairRight (DirectEnumerator.unpairRight ha))))
                (add DirectEnumerator.cache
                  (DirectEnumerator.unpairLeft (DirectEnumerator.unpairRight ha)))
                (DirectScalar.sub (DirectEnumerator.unpairLeft ha) (constant 3)))
              (DirectEnumerator.stack
                (add DirectEnumerator.depth (DirectEnumerator.unpairLeft
                  (DirectEnumerator.unpairRight (DirectEnumerator.unpairRight ha))))
                DirectEnumerator.cache
                (add DirectEnumerator.cache
                  (DirectEnumerator.unpairLeft (DirectEnumerator.unpairRight ha)))
                (DirectScalar.sub (DirectEnumerator.unpairLeft ha) (constant 3))
                DirectEnumerator.depth DirectEnumerator.tw DirectEnumerator.ws)
              Realizes.zero Realizes.zero))))).val := rfl

/-- One raw command step of the program agrees with `execValue` of the machine,
for an arbitrary raw command `raw` and next-candidate counter `q`. -/
theorem rel_rawStep {a b : ℕ → ℕ} (ha : R a) (hb : R b) {n pl np tw ws d h raw q : V}
    (hn : n = encV pl np tw ws d h) (hraw : evalV ha.val n = raw) (hq : evalV hb.val n = q) :
    StateRel (evalV (DirectEnumerator.rawStepProgram ha hb).val n)
      (execValue raw q (stateValue tw ws d h)) := by
  have hTW := reg_tw hn
  have hWS := reg_ws hn
  have hD := reg_depth hn
  have hH := reg_cache hn
  have c0 : evalV (DirectEnumerator.unpairLeft ha).val n = evalV (constant 0).val n ↔
      first raw = 0 := by
    simp only [evalV_unpairLeft, hraw, evalV_constant, Nat.cast_zero, iff_self]
  have c1 : evalV (DirectEnumerator.unpairLeft ha).val n = evalV (constant 1).val n ↔
      first raw = 1 := by
    simp only [evalV_unpairLeft, hraw, evalV_constant, Nat.cast_one, iff_self]
  have c2 : evalV (DirectEnumerator.unpairLeft ha).val n = evalV (constant 2).val n ↔
      first raw = 2 := by
    simp only [evalV_unpairLeft, hraw, evalV_constant, Nat.cast_ofNat, iff_self]
  have cc : evalV DirectEnumerator.cache.val n = evalV (constant 1).val n ↔ h = 1 := by
    simp only [hH, evalV_constant, Nat.cast_one, iff_self]
  have cm : evalV (DirectEnumerator.implication DirectEnumerator.tw
        (add DirectEnumerator.depth
          (DirectEnumerator.unpairLeft (DirectEnumerator.unpairRight ha)))).val n =
        evalV DirectEnumerator.cache.val n ↔ wim tw (d + first (second raw)) = h := by
    simp only [evalV_implication, hTW, evalV_add, hD, evalV_unpairLeft, evalV_unpairRight, hraw,
      hH, iff_self]
  rw [rawStepProgram_val, evalV_ifEq]
  by_cases hk0 : first raw = 0
  · -- `NIP`: halt on a cached truth, otherwise pop the working stack.
    rw [if_pos (c0.mpr hk0), evalV_ifEq]
    by_cases hh : h = 1
    · have hs : stepValue raw (stateValue tw ws d h) = 0 := by
        rw [stepValue_state, effect_k0_halt hk0 hh]
      rw [if_pos (cc.mpr hh), evalV_zeroR, exec_of_step_zero hs]
      exact Or.inl ⟨rfl, rfl⟩
    · have hs : stepValue raw (stateValue tw ws d h) = someState tw (second ws) d (first ws) := by
        rw [stepValue_state, effect_k0_live hk0 hh]
      rw [if_neg (fun e => hh (cc.mp e)), exec_of_step hs,
        tail_lt_two (show first raw < 2 by rw [hk0]; exact zero_lt_two)]
      simp only [evalV_successor, evalV_state, evalV_unpairLeft, evalV_unpairRight, hraw, hq,
        hTW, hWS, hD, hH]
      exact Or.inr ⟨_, _, _, _, _, _, rfl, rfl⟩
  · rw [if_neg (fun e => hk0 (c0.mp e)), evalV_ifEq]
    by_cases hk1 : first raw = 1
    · -- `DROP`.
      have hs : stepValue raw (stateValue tw ws d h) = someState h (cantor tw ws) d h := by
        rw [stepValue_state, effect_k1 hk1]
      rw [if_pos (c1.mpr hk1), exec_of_step hs,
        tail_lt_two (show first raw < 2 by rw [hk1]; exact one_lt_two)]
      simp only [evalV_successor, evalV_state, evalV_unpairRight, evalV_cantorPair, hraw, hq,
        hTW, hWS, hD, hH]
      exact Or.inr ⟨_, _, _, _, _, _, rfl, rfl⟩
    · rw [if_neg (fun e => hk1 (c1.mp e)), evalV_ifEq]
      by_cases hk2 : first raw = 2
      · -- `MP`.
        rw [if_pos (c2.mpr hk2), evalV_ifEq]
        by_cases hm : wim tw (d + first (second raw)) = h
        · have hs : stepValue raw (stateValue tw ws d h) =
              someState (d + first (second raw)) (cantor 0 ws) (d + first (second raw)) 0 := by
            rw [stepValue_state, effect_k2_mp hk2 hm]
          rw [if_pos (cm.mpr hm), exec_of_step hs, tail_two hk2]
          simp only [evalV_successor, evalV_state, evalV_unpairLeft, evalV_unpairRight,
            evalV_add, evalV_cantorPair, evalV_zeroR, hraw, hq, hTW, hWS, hD, hH]
          exact Or.inr ⟨_, _, _, _, _, _, rfl, rfl⟩
        · have hs : stepValue raw (stateValue tw ws d h) =
              someState 0 ws (d + first (second raw)) 0 := by
            rw [stepValue_state, effect_k2_skip hk2 hm]
          rw [if_neg (fun e => hm (cm.mp e)), exec_of_step hs, tail_two hk2]
          simp only [evalV_successor, evalV_state, evalV_unpairLeft, evalV_unpairRight,
            evalV_add, evalV_zeroR, hraw, hq, hTW, hWS, hD, hH]
          exact Or.inr ⟨_, _, _, _, _, _, rfl, rfl⟩
      · -- `AX` with gate label `first raw - 3`.
        rw [if_neg (fun e => hk2 (c2.mp e))]
        have hs : stepValue raw (stateValue tw ws d h) =
            someState (gateValue (d + first (second (second raw))) (h + first (second raw))
              (first raw - 3))
              (axStackValue (d + first (second (second raw))) h (h + first (second raw))
                (first raw - 3) d tw ws) 0 0 := by
          rw [stepValue_state, effect_k3 hk0 hk1 hk2]
        rw [exec_of_step hs, tail_three hk0 hk1 hk2]
        simp only [evalV_successor, evalV_state, evalV_unpairLeft, evalV_unpairRight, evalV_add,
          evalV_sub, evalV_constant, Nat.cast_ofNat, evalV_gated, evalV_stack, evalV_zeroR, hraw,
          hq, hTW, hWS, hD, hH]
        exact Or.inr ⟨_, _, _, _, _, _, rfl, rfl⟩

/-! ### Fetching and the full step -/

section Fetch
variable {n pl np tw ws d h : V}

theorem evalV_newPl (hn : n = encV pl np tw ws d h) :
    evalV (ifEq DirectEnumerator.pl (constant 0) DirectEnumerator.np
      (DirectScalar.sub DirectEnumerator.pl (constant 1))).val n = first (fetchValue pl np) := by
  have cp : evalV DirectEnumerator.pl.val n = evalV (constant 0).val n ↔ pl = 0 := by
    simp only [reg_pl hn, evalV_constant, Nat.cast_zero, iff_self]
  rw [evalV_ifEq]
  by_cases hp : pl = 0
  · rw [if_pos (cp.mpr hp), reg_np hn, hp, raw_new]
  · rw [if_neg (fun e => hp (cp.mp e)), evalV_sub, reg_pl hn, evalV_constant, Nat.cast_one]
    obtain ⟨m, rfl⟩ : ∃ m : V, pl = m + 1 := ⟨pl - 1, (ModelOptimizer.sub_one_add_one hp).symm⟩
    rw [add_tsub_cancel_right, raw_continuation]

theorem evalV_newNp (hn : n = encV pl np tw ws d h) :
    evalV (ifEq DirectEnumerator.pl (constant 0) (successor DirectEnumerator.np)
      DirectEnumerator.np).val n = second (fetchValue pl np) := by
  have cp : evalV DirectEnumerator.pl.val n = evalV (constant 0).val n ↔ pl = 0 := by
    simp only [reg_pl hn, evalV_constant, Nat.cast_zero, iff_self]
  rw [evalV_ifEq]
  by_cases hp : pl = 0
  · rw [if_pos (cp.mpr hp), evalV_successor, reg_np hn, hp, next_new]
  · rw [if_neg (fun e => hp (cp.mp e)), reg_np hn]
    obtain ⟨m, rfl⟩ : ∃ m : V, pl = m + 1 := ⟨pl - 1, (ModelOptimizer.sub_one_add_one hp).symm⟩
    rw [next_continuation]

/-- `Realizes.ofEq` keeps the program; stated generically so that no concrete
program is unfolded by the definitional check. -/
theorem ofEq_val {f g : ℕ → ℕ} (p : ScalarPRCode.Realizes f) (h : ∀ n, f n = g n) :
    (p.ofEq h).val = p.val := rfl

theorem enumStepProgram_val : DirectEnumerator.enumStepProgram.val =
    (DirectEnumerator.rawStepProgram
      (ifEq DirectEnumerator.pl (constant 0) DirectEnumerator.np
        (DirectScalar.sub DirectEnumerator.pl (constant 1)))
      (ifEq DirectEnumerator.pl (constant 0) (successor DirectEnumerator.np)
        DirectEnumerator.np)).val := by
  unfold DirectEnumerator.enumStepProgram
  exact ofEq_val _ _

/-- The program's fetch-and-execute step is the machine's `execValue` of the
fetched pair. -/
theorem rel_enumStep (hn : n = encV pl np tw ws d h) :
    StateRel (evalV DirectEnumerator.enumStepProgram.val n)
      (execValue (first (fetchValue pl np)) (second (fetchValue pl np)) (stateValue tw ws d h)) := by
  rw [enumStepProgram_val]
  exact rel_rawStep _ _ hn (evalV_newPl hn) (evalV_newNp hn)

end Fetch

theorem optionStepProgram_val : DirectEnumerator.optionStepProgram.val =
    (ifZero identity Realizes.zero
      (DirectEnumerator.enumStepProgram.comp (DirectScalar.sub identity (constant 1)))).val := rfl

/-- One program step and one machine step preserve the state relation. -/
theorem rel_optionStep {x m : V} (hr : StateRel x m) :
    StateRel (evalV DirectEnumerator.optionStepProgram.val x) (enumValue m) := by
  rw [optionStepProgram_val, evalV_ifZero, evalV_identity]
  rcases hr with ⟨hx, hm⟩ | ⟨pl, np, tw, ws, d, h, hx, hm⟩
  · rw [if_pos hx, evalV_zeroR, hm, enum_zero]
    exact Or.inl ⟨rfl, rfl⟩
  · have hx0 : x ≠ 0 := by
      rw [hx]
      exact succ_ne_zero' _
    rw [if_neg hx0, evalV_compR, evalV_sub, evalV_identity, evalV_constant, Nat.cast_one, hx,
      add_tsub_cancel_right, hm, enum_live]
    exact rel_enumStep rfl

end DiophantineConsistency.ModelEnumeratorStep
