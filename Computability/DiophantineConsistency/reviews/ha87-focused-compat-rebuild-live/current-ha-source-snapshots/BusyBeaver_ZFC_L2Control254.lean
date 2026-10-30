import BusyBeaver.ZFC.L2Macros254

/-!
Control subroutines of the 219-node program (L2, part 3): the destructive
equality test, the fetch of the next command, and the MP and NIP branches.

`if_eq(scratch1, param2, body)` decrements both registers together; the
body runs iff they were equal, and both are zero afterwards.
-/

namespace SetTheory.BusyBeaver.ZFC.L2

open RMDag Dag254 Code254

attribute [local irreducible] Code254.P

def dist (a b : Nat) : Nat := if b ≥ a then b - a else a - b

/-- The joint decrement loop (node 124). -/
theorem loop124 : ∀ (a : Nat) (st : AS), st.s1 = a →
    Rn (.node 124) st { st with s1 := 0, p2 := dist st.s1 st.p2 }
  | 0, st, ha => by
      apply rn_eq (skip (p := dag254) (n := 124) rfl (Run.decZero 6 (enc st) (by simp [enc, ha])))
      cases st; simp only at ha; subst ha; simp [dist]
  | a + 1, st, ha => by
      have hdec := Run.decPos (p := dag254) 6 (enc st) a (by simp [enc, ha])
      rw [upd_s1] at hdec
      by_cases hp : st.p2 = 0
      · -- param2 exhausted: move the remainder back and stop.
        have h126 : Rn (.node 126) { st with s1 := a } { st with s1 := a } :=
          skip (p := dag254) (n := 126) rfl (Run.decZero 5 _ (by simp [enc, hp]))
        have h127 : Rn (.node 127) { st with s1 := a } { st with s1 := 0, p2 := st.p2 + a + 1 } :=
          rn_eq (seqAS (n := 127) rfl (loop207 _) (inc_AS 5 (by omega) _)) (by simp [updAS, enc])
        apply rn_eq (seqAS (n := 124) rfl hdec (seqAS (n := 125) rfl h126 h127))
        cases st; simp only at ha hp; subst ha hp; simp [dist]
      · obtain ⟨b, hb⟩ : ∃ b, st.p2 = b + 1 := ⟨st.p2 - 1, by omega⟩
        have hdec5 := Run.decPos (p := dag254) 5 (enc { st with s1 := a }) b (by simp [enc, hb])
        rw [upd_p2] at hdec5
        have h126 : Run dag254 (.node 126) (enc { st with s1 := a }) (.cont 1)
            (enc { { st with s1 := a } with p2 := b }) :=
          cont_cdr (p := dag254) (n := 126) (k := 0) rfl hdec5 (Run.contS 1 _)
        have h125 : Run dag254 (.node 125) (enc { st with s1 := a }) (.cont 1)
            (enc { { st with s1 := a } with p2 := b }) :=
          Run.carCont 125 0 _ _ (by exact h126)
        apply rn_eq (restart (p := dag254) (n := 124) rfl hdec h125
          (loop124 a { { st with s1 := a } with p2 := b } rfl))
        cases st; simp only at ha hb; subst ha hb; simp [dist]

theorem dist_eq_zero {a b : Nat} : dist a b = 0 ↔ a = b := by
  unfold dist; split <;> omega

/-- The equality test (node 123): normal iff equal, otherwise break one level. -/
theorem ifeq_eq (st : AS) (h : st.s1 = st.p2) :
    Run dag254 (.node 123) (enc st) .normal (enc { st with s1 := 0, p2 := 0 }) := by
  have hz : enc { st with s1 := 0, p2 := dist st.s1 st.p2 } 5 = 0 := by
    simp [enc, dist_eq_zero.mpr h]
  have h128 := skip (p := dag254) (n := 128) rfl (Run.decZero 5 _ hz)
  apply rn_eq (seqAS (n := 123) rfl (loop124 st.s1 st rfl) h128)
  simp [dist_eq_zero.mpr h]

theorem ifeq_ne (st : AS) (h : st.s1 ≠ st.p2) :
    Run dag254 (.node 123) (enc st) (.brk 1) (enc { st with s1 := 0, p2 := 0 }) := by
  have h124 := loop124 st.s1 st rfl
  obtain ⟨c, hc⟩ : ∃ c, dist st.s1 st.p2 = c + 1 := ⟨dist st.s1 st.p2 - 1, by
    have := (not_congr dist_eq_zero).mpr h; omega⟩
  have hdec := Run.decPos (p := dag254) 5 (enc { st with s1 := 0, p2 := dist st.s1 st.p2 }) c
    (by simp [enc, hc])
  rw [upd_p2] at hdec
  have h129 : Run dag254 (.node 129) (enc { { st with s1 := 0, p2 := dist st.s1 st.p2 } with p2 := c })
      (.brk 1) (enc { st with s1 := 0, p2 := 0 }) := by
    have hc199 := loop199 { { st with s1 := 0, p2 := dist st.s1 st.p2 } with p2 := c }
    have h' := brk_cdr (p := dag254) (n := 129) (k := 0) rfl hc199 (Run.brkS 0 _)
    have e : ({ { { st with s1 := 0, p2 := dist st.s1 st.p2 } with p2 := c } with p2 := 0 } : AS) =
        { st with s1 := 0, p2 := 0 } := by cases st; rfl
    rwa [e] at h'
  have h128 := brk_cdr (p := dag254) (n := 128) (k := 0) rfl hdec h129
  exact brk_cdr (p := dag254) (n := 123) (k := 0) rfl h124 h128

/-! ## Uses of the equality test -/

/-- `if_eq(s1, param2, par1)` (node 130). -/
theorem ifeq_par1 (st : AS) (h2 : st.s2 = 0) :
    Rn (.node 130) st (if st.s1 = st.p2
      then { st with s1 := 0, p2 := 0, tw := st.p1, ws := P st.tw st.ws }
      else { st with s1 := 0, p2 := 0 }) := by
  by_cases h : st.s1 = st.p2
  · rw [if_pos h]; exact seqAS (n := 130) rfl (ifeq_eq st h) (par1 _ ⟨rfl, h2⟩)
  · rw [if_neg h]; exact skip (p := dag254) (n := 130) rfl (ifeq_ne st h)

/-- `if_eq(s1, param2, clear tw)` (node 131), the gate test. -/
theorem ifeq_clear (st : AS) :
    Rn (.node 131) st (if st.s1 = st.p2
      then { st with s1 := 0, p2 := 0, tw := 0 } else { st with s1 := 0, p2 := 0 }) := by
  by_cases h : st.s1 = st.p2
  · rw [if_pos h]; exact seqAS (n := 131) rfl (ifeq_eq st h) (loop214 _)
  · rw [if_neg h]; exact skip (p := dag254) (n := 131) rfl (ifeq_ne st h)

/-! ## Fetch, MP and NIP -/

/-- The fetch (node 133): a nonzero proof list is decremented; an exhausted
one loads the next candidate. -/
theorem fetch_pos (st : AS) (v : Nat) (hv : st.pl = v + 1) : Rn (.node 133) st { st with pl := v } := by
  have hdec := Run.decPos (p := dag254) 8 (enc st) v (by simp [enc, hv])
  rw [upd_pl] at hdec
  have h134 := brk_cdr (p := dag254) (n := 134) (k := 0) rfl hdec (Run.brkS 0 _)
  exact skip (p := dag254) (n := 133) rfl h134

theorem fetch_zero (st : AS) (hpl : st.pl = 0) (h1 : st.s1 = 0) :
    Rn (.node 133) st { st with pl := st.np, np := st.np + 1 } := by
  have h134 : Rn (.node 134) st st :=
    skip (p := dag254) (n := 134) rfl (Run.decZero 8 (enc st) (by simp [enc, hpl]))
  have h135 := seqAS (n := 135) rfl (loop194 st)
    (seqAS (n := 136) rfl (loop203 _) (inc_AS 0 (by omega) _))
  apply rn_eq (seqAS (n := 133) rfl h134 h135)
  cases st; simp only at hpl h1; subst hpl h1; simp [updAS, enc]

/-- The MP branch (node 150). -/
theorem mp_branch (st : AS) (hc : Clean st) :
    Rn (.node 150) st (if wim st.tw st.p1 = st.p2
      then { st with tw := st.p1, ws := P 0 st.ws, p2 := 0 }
      else { st with tw := 0, p2 := 0 }) := by
  apply rn_eq (seqAS (n := 150) rfl (seqAS (n := 161) rfl (par1 st hc) (cons _ hc))
    (seqAS (n := 151) rfl (loop216 _) (ifeq_par1 _ hc.2)))
  obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1 h2
  simp only [ofNat_P, Nat.zero_add]

/-- The NIP branch (node 152) when the cache is not the falsity code. -/
theorem nip_branch (st : AS) (hc : Clean st) (hh : st.p2 ≠ 1) :
    Rn (.node 152) st { st with p2 := (Cantor.ofNat st.ws).1, ws := (Cantor.ofNat st.ws).2 } := by
  have hne : (updAS st 6 (enc st 6 + 1)).s1 ≠ (updAS st 6 (enc st 6 + 1)).p2 := by
    simp only [updAS, enc, hc.1]; omega
  have h132 := skip (p := dag254) (n := 132) rfl (ifeq_ne _ hne)
  have h153 := seqAS (n := 153) rfl h132 (pop_p2 _ ⟨rfl, hc.2⟩)
  apply rn_eq (seqAS (n := 152) rfl (inc_AS 6 (by omega) st) h153)
  obtain ⟨h1, h2⟩ := hc; cases st; simp only at h1 h2; subst h1 h2; simp [updAS, enc]

/-- The NIP branch halts on the falsity code. -/
theorem nip_halt (st : AS) (hc : Clean st) (hh : st.p2 = 1) :
    ∃ R', Run dag254 (.node 152) (enc st) .halt R' := by
  have heq : (updAS st 6 (enc st 6 + 1)).s1 = (updAS st 6 (enc st 6 + 1)).p2 := by
    simp only [updAS, enc, hc.1, hh]
  have h132 := halt_cdr (p := dag254) (n := 132) rfl (ifeq_eq _ heq) (Run.halt _)
  have h153 := halt_car (p := dag254) (n := 153) rfl h132
  exact ⟨_, halt_cdr (p := dag254) (n := 152) rfl (inc_AS 6 (by omega) st) h153⟩

end SetTheory.BusyBeaver.ZFC.L2
