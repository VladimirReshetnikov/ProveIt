import BusyBeaver.ZFC.ArithmeticL2Macros254

set_option autoImplicit false

/-!
# Internal L2, part 3: control subroutines of the 219-node program

The internal counterpart of `L2Control254`, in every model of `IΣ₁`: the
destructive equality test `if_eq(scratch1, param2, body)` (which decrements
both registers together; the body runs iff they were equal, and both are zero
afterwards), the fetch of the next command, and the MP and NIP branches.
-/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticL2

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticDagRun RMDag
open ArithmeticControlFile (writeValue)
open ArithmeticCode254 (wim wel wal weq tagged)

set_option maxRecDepth 8192
set_option maxHeartbeats 400000

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Absolute difference. -/
noncomputable def dist (a b : V) : V := if a ≤ b then b - a else a - b

theorem dist_eq_zero {a b : V} : dist a b = 0 ↔ a = b := by
  unfold dist
  split_ifs with h
  · rw [tsub_eq_zero_iff_le]
    exact ⟨fun h' => le_antisymm h h', fun h' => h' ▸ le_rfl⟩
  · rw [tsub_eq_zero_iff_le]
    exact ⟨fun h' => absurd h' (fun h'' => h (le_of_lt (lt_of_le_of_ne h'' (fun e => h (e ▸ le_rfl))))),
      fun h' => absurd (h' ▸ le_rfl) h⟩

/-- The joint decrement loop (node 124). -/
theorem loop124 (st : AS V) : Rn (.node 124) st { st with s1 := 0, p2 := dist st.s1 st.p2 } := by
  set a := st.s1
  set b := st.p2
  obtain ⟨N, hNdef⟩ : ∃ N : V, N = min a b := ⟨_, rfl⟩
  let Gr : V → AS V := fun t => { st with s1 := a - t, p2 := b - t }
  let Hr : V → AS V := fun t => { st with s1 := a - t - 1, p2 := b - t }
  let x0 : V := enc st
  -- logical s1 and p2 are the physical fields 8 and 7
  let G : V → V := fun t =>
    writeValue ((7 : Nat) : V) (b - t) (writeValue ((8 : Nat) : V) (a - t) x0)
  have hG : ∀ t, G t = enc (Gr t) := by
    intro t
    show lupd (lupd (enc st) 6 (a - t)) 5 (b - t) = enc (Gr t)
    rw [lupd_enc _ 6 (by omega), lupd_enc _ 5 (by omega)]
    rfl
  haveI : 𝚺₁-Function₁[V] G :=
    write2_definable _ _ (fun t => b - t) (fun t => a - t) x0 (sub_definable b) (sub_definable a)
  have hpass : ∀ t, t < N → IR (.decnz 6) (G t) .normal (enc (Hr t)) ∧
      IR (.node 125) (enc (Hr t)) (.cont 1) (G (t+1)) := by
    intro t ht
    have hta : t < a := lt_of_lt_of_le ht (hNdef ▸ min_le_left a b)
    have htb : t < b := lt_of_lt_of_le ht (hNdef ▸ min_le_right a b)
    refine ⟨?_, ?_⟩
    · rw [hG]
      exact decPos_AS 6 (by omega) (Gr t) (a - t - 1)
        (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt hta))).symm
    · rw [hG]
      have hdec := decPos_AS 5 (by omega) (Hr t) (b - t - 1)
        (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt htb))).symm
      have h126 := R.cont_cdr (n := 126) (k := 0) rfl hdec (R.contS 1 _)
      have h125 := R.cont_car (n := 125) (k := 0) rfl h126
      have e : updAS (Hr t) 5 (b - t - 1) = Gr (t+1) := by
        show ({ st with s1 := a - t - 1, p2 := b - t - 1 } : AS V) = { st with s1 := a - (t+1), p2 := b - (t+1) }
        rw [tsub_tsub, tsub_tsub]
      rwa [e] at h125
  have hfin : IR (.node 124) (G N) .normal (enc { st with s1 := 0, p2 := dist a b }) := by
    rw [hG]
    by_cases hab : a ≤ b
    · have hN : N = a := hNdef.trans (min_eq_left hab)
      have h := R.skip (n := 124) rfl (decZero_AS 6 (by omega) (Gr N) (by
        show a - N = 0; rw [hN, tsub_self]))
      have e : Gr N = { st with s1 := 0, p2 := dist a b } := by
        show ({ st with s1 := a - N, p2 := b - N } : AS V) = _
        rw [hN, tsub_self, dist, if_pos hab]
      rw [← e]; exact h
    · have hba : b ≤ a := le_of_lt (lt_of_not_ge hab)
      have hN : N = b := hNdef.trans (min_eq_right hba)
      have hpos : 0 < a - b := tsub_pos_of_lt (lt_of_not_ge hab)
      have hdec := decPos_AS 6 (by omega) (Gr N) (a - b - 1) (by
        show a - N = a - b - 1 + 1
        rw [hN]
        exact (tsub_add_cancel_of_le (one_le_of_pos hpos)).symm)
      have h126 := R.skip (n := 126) rfl (decZero_AS 5 (by omega) (updAS (Gr N) 6 (a - b - 1)) (by
        show b - N = 0; rw [hN, tsub_self]))
      have h127 := R.seq (n := 127) rfl (loop207 (updAS (Gr N) 6 (a - b - 1)))
        (inc_AS 5 (by omega) _)
      have h125 := R.seq (n := 125) rfl h126 h127
      have h := R.seq (n := 124) rfl hdec h125
      have e : updAS { (updAS (Gr N) 6 (a - b - 1)) with
          p2 := (updAS (Gr N) 6 (a - b - 1)).p2 + (updAS (Gr N) 6 (a - b - 1)).s1, s1 := 0 } 5
          (field { (updAS (Gr N) 6 (a - b - 1)) with
            p2 := (updAS (Gr N) 6 (a - b - 1)).p2 + (updAS (Gr N) 6 (a - b - 1)).s1, s1 := 0 } 5 + 1)
          = { st with s1 := 0, p2 := dist a b } := by
        show ({ st with s1 := 0, p2 := b - N + (a - b - 1) + 1 } : AS V) = _
        rw [hN, tsub_self, zero_add, tsub_add_cancel_of_le (one_le_of_pos hpos), dist, if_neg hab]
      rw [← e]; exact h
  have hit := R.iterate (n := 124) rfl G (fun t => enc (Hr t)) N hpass hfin
  have hG0 : G 0 = enc st := by
    rw [hG]
    congr 1
    show ({ st with s1 := a - 0, p2 := b - 0 } : AS V) = st
    rw [tsub_zero, tsub_zero]
  rwa [hG0] at hit

/-- The equality test (node 123): normal iff equal, otherwise break one level. -/
theorem ifeq_eq (st : AS V) (h : st.s1 = st.p2) :
    IR (.node 123) (enc st) .normal (enc { st with s1 := 0, p2 := 0 }) := by
  have h124 := loop124 st
  have hz : field { st with s1 := 0, p2 := dist st.s1 st.p2 } 5 = 0 := dist_eq_zero.mpr h
  have h128 := R.skip (n := 128) rfl (decZero_AS 5 (by omega) _ hz)
  have := R.seq (n := 123) rfl h124 h128
  apply rn_eq this
  simp [dist_eq_zero.mpr h]

theorem ifeq_ne (st : AS V) (h : st.s1 ≠ st.p2) :
    IR (.node 123) (enc st) (.brk 1) (enc { st with s1 := 0, p2 := 0 }) := by
  have h124 := loop124 st
  have hd : dist st.s1 st.p2 ≠ 0 := fun e => h (dist_eq_zero.mp e)
  have hc : dist st.s1 st.p2 = (dist st.s1 st.p2 - 1) + 1 :=
    (tsub_add_cancel_of_le (one_le_of_pos (lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm hd)))).symm
  have hdec := decPos_AS 5 (by omega) { st with s1 := 0, p2 := dist st.s1 st.p2 }
    (dist st.s1 st.p2 - 1) hc
  have h129 : IR (.node 129) (enc (updAS { st with s1 := 0, p2 := dist st.s1 st.p2 } 5
      (dist st.s1 st.p2 - 1))) (.brk 1) (enc { st with s1 := 0, p2 := 0 }) := by
    have hc199 := loop199 (updAS { st with s1 := 0, p2 := dist st.s1 st.p2 } 5 (dist st.s1 st.p2 - 1))
    have h' := R.brk_cdr (n := 129) (k := 0) rfl hc199 (R.brkS 0 _)
    exact h'
  have h128 := R.brk_cdr (n := 128) (k := 0) rfl hdec h129
  exact R.brk_cdr (n := 123) (k := 0) rfl h124 h128

/-! ## Uses of the equality test -/

/-- `if_eq(s1, param2, par1)` (node 130). -/
theorem ifeq_par1 (st : AS V) (h2 : st.s2 = 0) :
    Rn (.node 130) st (if st.s1 = st.p2
      then { st with s1 := 0, p2 := 0, tw := st.p1, ws := cantor st.tw st.ws }
      else { st with s1 := 0, p2 := 0 }) := by
  by_cases h : st.s1 = st.p2
  · rw [if_pos h]
    exact R.seq (n := 130) rfl (ifeq_eq st h) (par1 _ ⟨rfl, h2⟩)
  · rw [if_neg h]
    exact R.skip (n := 130) rfl (ifeq_ne st h)

/-- `if_eq(s1, param2, clear tw)` (node 131), the gate test. -/
theorem ifeq_clear (st : AS V) :
    Rn (.node 131) st (if st.s1 = st.p2
      then { st with s1 := 0, p2 := 0, tw := 0 } else { st with s1 := 0, p2 := 0 }) := by
  by_cases h : st.s1 = st.p2
  · rw [if_pos h]
    exact R.seq (n := 131) rfl (ifeq_eq st h) (loop214 _)
  · rw [if_neg h]
    exact R.skip (n := 131) rfl (ifeq_ne st h)

/-! ## Fetch, MP and NIP -/

/-- The fetch (node 133): a nonzero proof list is decremented; an exhausted
one loads the next candidate. -/
theorem fetch_pos (st : AS V) (v : V) (hv : st.pl = v + 1) : Rn (.node 133) st { st with pl := v } := by
  have hdec := decPos_AS 8 (by omega) st v hv
  have h134 := R.brk_cdr (n := 134) (k := 0) rfl hdec (R.brkS 0 _)
  exact R.skip (n := 133) rfl h134

theorem fetch_zero (st : AS V) (hpl : st.pl = 0) (h1 : st.s1 = 0) :
    Rn (.node 133) st { st with pl := st.np, np := st.np + 1 } := by
  have h134 : Rn (.node 134) st st := R.skip (n := 134) rfl (decZero_AS 8 (by omega) st hpl)
  have h135 := R.seq (n := 135) rfl (loop194 st)
    (R.seq (n := 136) rfl (loop203 _) (inc_AS 0 (by omega) _))
  have := R.seq (n := 133) rfl h134 h135
  apply rn_eq this
  cases st; simp only at hpl h1; subst hpl; subst h1; simp [updAS, field]

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
  have h132 := R.halt_cdr (n := 132) rfl (ifeq_eq _ heq) (R.halt _)
  have h153 := R.halt_car (n := 153) rfl h132
  exact ⟨_, R.halt_cdr (n := 152) rfl hinc h153⟩

end SetTheory.BusyBeaver.ZFC.ArithmeticL2
