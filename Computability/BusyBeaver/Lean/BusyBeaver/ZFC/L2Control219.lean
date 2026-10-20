/- Forked by Research/ZFC/k225-formal/generate_l2q219.py from L2Control222.lean for dag219 (dag222 with Source 140's equality test); do not edit. -/
import BusyBeaver.ZFC.L2Macros219

/-!
Control subroutines of the 219-node program (L2, part 3): the destructive
equality test, the fetch of the next command, and the MP and NIP branches.

`if_eq(scratch1, param2, body)` decrements both registers together; the
body runs iff they were equal, and both are zero afterwards.
-/

namespace SetTheory.BusyBeaver.ZFC.L2Q

open RMDag Dag219 Code254

attribute [local irreducible] Code254.P

def dist (a b : Nat) : Nat := if b ≥ a then b - a else a - b

/-! ## The equality test: Source 140's routine (nodes 123, 461-466)

`P = (D6, C2)` (461), `U = (P, B)` (462), `A = (D5, U)` (463), `L = (A, D6)` (464),
`Z = (D5, C1)` (465), `R = (Z, U)` (466), `E = (L, R)` (123); `D6` decrements `s1` and `D5`
decrements `p2`. `A` cancels the two counters, `L` breaks exactly on equality, `R` clears both
and breaks; so `E` returns normally iff `s1 = p2`, and leaves both zero. -/

theorem run_eq' {e : Edge} {s s1 s2 : AS} {x : Exit} (h : Run dag219 e (enc s) x (enc s1))
    (he : s1 = s2) : Run dag219 e (enc s) x (enc s2) := he ▸ h

theorem eqP_pos (st : AS) (b : Nat) (h : st.s1 = b + 1) :
    Run dag219 (.node 461) (enc st) (.cont 1) (enc { st with s1 := b }) := by
  have hdec := Run.decPos (p := dag219) 6 (enc st) b (by simp [enc, h])
  rw [upd_s1] at hdec
  exact cont_cdr (p := dag219) (n := 461) (k := 0) rfl hdec (Run.contS 1 _)

theorem eqP_zero (st : AS) (h : st.s1 = 0) :
    Run dag219 (.node 461) (enc st) .normal (enc st) :=
  skip (p := dag219) (n := 461) rfl (Run.decZero 6 (enc st) (by simp [enc, h]))

theorem eqU_pos (st : AS) (b : Nat) (h : st.s1 = b + 1) :
    Run dag219 (.node 462) (enc st) (.cont 1) (enc { st with s1 := b }) :=
  Run.carCont 462 0 _ _ (by exact eqP_pos st b h)

theorem eqU_zero (st : AS) (h : st.s1 = 0) :
    Run dag219 (.node 462) (enc st) (.brk 1) (enc st) :=
  brk_cdr (p := dag219) (n := 462) (k := 0) rfl (eqP_zero st h) (Run.brkS 0 _)

/-- The cancellation loop `A`. -/
theorem eqA : ∀ (a : Nat) (st : AS), st.p2 = a →
    (a ≤ st.s1 → Run dag219 (.node 463) (enc st) .normal (enc { st with p2 := 0, s1 := st.s1 - a })) ∧
    (st.s1 < a → Run dag219 (.node 463) (enc st) (.brk 1) (enc { st with p2 := a - st.s1 - 1, s1 := 0 }))
  | 0, st, ha => by
      refine ⟨fun _ => ?_, fun h => absurd h (Nat.not_lt_zero _)⟩
      have h := skip (p := dag219) (n := 463) rfl (Run.decZero 5 (enc st) (by simp [enc, ha]))
      apply run_eq' h
      cases st; simp only at ha; subst ha; simp
  | a + 1, st, ha => by
      have hdec := Run.decPos (p := dag219) 5 (enc st) a (by simp [enc, ha])
      rw [upd_p2] at hdec
      rcases Nat.eq_zero_or_pos st.s1 with hs | hs
      · refine ⟨fun h => by omega, fun _ => ?_⟩
        have hU := eqU_zero { st with p2 := a } (by simpa using hs)
        have := brk_cdr (p := dag219) (n := 463) (k := 0) rfl hdec hU
        apply run_eq' this
        cases st; simp only at ha hs; subst ha; subst hs; simp
      · obtain ⟨b, hb⟩ : ∃ b, st.s1 = b + 1 := ⟨st.s1 - 1, by omega⟩
        have hU := eqU_pos { st with p2 := a } b (by simpa using hb)
        obtain ⟨ih1, ih2⟩ := eqA a { { st with p2 := a } with s1 := b } rfl
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have := restart (p := dag219) (n := 463) rfl hdec hU (ih1 (show a ≤ b by omega))
          apply run_eq' this
          cases st; dsimp only at ha hb ⊢; subst ha; subst hb; congr 1 <;> omega
        · have := restart (p := dag219) (n := 463) rfl hdec hU (ih2 (show b < a by omega))
          apply run_eq' this
          cases st; dsimp only at ha hb ⊢; subst ha; subst hb; congr 1 <;> omega

theorem eqL_eq (st : AS) (h : st.s1 = st.p2) :
    Run dag219 (.node 464) (enc st) (.brk 1) (enc { st with p2 := 0, s1 := 0 }) := by
  have hA := (eqA st.p2 st rfl).1 (by omega)
  have hz : enc { st with p2 := 0, s1 := st.s1 - st.p2 } 6 = 0 := by simp [enc, h]
  have := brk_cdr (p := dag219) (n := 464) (k := 0) rfl hA (Run.decZero 6 _ hz)
  apply run_eq' this
  cases st; simp only at h; subst h; simp

theorem eqL_ne (st : AS) (h : st.s1 ≠ st.p2) :
    ∃ x y, Run dag219 (.node 464) (enc st) .normal (enc { st with p2 := x, s1 := y }) := by
  rcases Nat.lt_or_gt_of_ne h with h' | h'
  · exact ⟨_, _, skip (p := dag219) (n := 464) rfl ((eqA st.p2 st rfl).2 h')⟩
  · obtain ⟨c, hc⟩ : ∃ c, st.s1 - st.p2 = c + 1 := ⟨st.s1 - st.p2 - 1, by omega⟩
    have hA := (eqA st.p2 st rfl).1 (by omega)
    have hdec := Run.decPos (p := dag219) 6 (enc { st with p2 := 0, s1 := st.s1 - st.p2 }) c
      (by simp [enc, hc])
    rw [upd_s1] at hdec
    exact ⟨0, c, run_eq' (seq (p := dag219) (n := 464) rfl hA hdec) (by cases st; rfl)⟩

/-- `Z` clears `p2`. -/
theorem eqZ : ∀ (a : Nat) (st : AS), st.p2 = a →
    Run dag219 (.node 465) (enc st) .normal (enc { st with p2 := 0 })
  | 0, st, ha => by
      have h := skip (p := dag219) (n := 465) rfl (Run.decZero 5 (enc st) (by simp [enc, ha]))
      apply run_eq' h
      cases st; simp only at ha; subst ha; rfl
  | a + 1, st, ha => by
      have hdec := Run.decPos (p := dag219) 5 (enc st) a (by simp [enc, ha])
      rw [upd_p2] at hdec
      have := restart (p := dag219) (n := 465) rfl hdec (Run.contS 0 _) (eqZ a { st with p2 := a } rfl)
      apply run_eq' this
      cases st; rfl

/-- `R` clears `p2`, then `s1`, and breaks. -/
theorem eqR : ∀ (b : Nat) (st : AS), st.s1 = b →
    Run dag219 (.node 466) (enc st) (.brk 1) (enc { st with p2 := 0, s1 := 0 })
  | 0, st, hb => by
      have hZ := eqZ st.p2 st rfl
      have hU := eqU_zero { st with p2 := 0 } (by simpa using hb)
      have := brk_cdr (p := dag219) (n := 466) (k := 0) rfl hZ hU
      apply run_eq' this
      cases st; simp only at hb; subst hb; rfl
  | b + 1, st, hb => by
      have hZ := eqZ st.p2 st rfl
      have hU := eqU_pos { st with p2 := 0 } b (by simpa using hb)
      have := restart (p := dag219) (n := 466) rfl hZ hU
        (eqR b { { st with p2 := 0 } with s1 := b } rfl)
      apply run_eq' this
      cases st; rfl

/-- The equality test (node 123): normal iff equal, otherwise break one level. -/
theorem ifeq_eq (st : AS) (h : st.s1 = st.p2) :
    Run dag219 (.node 123) (enc st) .normal (enc { st with s1 := 0, p2 := 0 }) := by
  have := skip (p := dag219) (n := 123) rfl (eqL_eq st h)
  apply run_eq' this
  cases st; rfl

theorem ifeq_ne (st : AS) (h : st.s1 ≠ st.p2) :
    Run dag219 (.node 123) (enc st) (.brk 1) (enc { st with s1 := 0, p2 := 0 }) := by
  obtain ⟨x, y, hL⟩ := eqL_ne st h
  have hR := eqR y { st with p2 := x, s1 := y } rfl
  have := brk_cdr (p := dag219) (n := 123) (k := 0) rfl hL hR
  apply run_eq' this
  cases st; rfl

/-! ## Uses of the equality test -/

/-- `if_eq(s1, param2, par1)` (node 130). -/
theorem ifeq_par1 (st : AS) (h2 : st.s2 = 0) :
    Rn (.node 130) st (if st.s1 = st.p2
      then { st with s1 := 0, p2 := 0, tw := st.p1, ws := P st.tw st.ws }
      else { st with s1 := 0, p2 := 0 }) := by
  by_cases h : st.s1 = st.p2
  · rw [if_pos h]
    exact seqAS (n := 130) rfl (ifeq_eq st h) (par1 _ ⟨rfl, h2⟩)
  · rw [if_neg h]
    exact skip (p := dag219) (n := 130) rfl (ifeq_ne st h)

/-- `if_eq(s1, param2, clear tw)` (node 131), the gate test. -/
theorem ifeq_clear (st : AS) :
    Rn (.node 131) st (if st.s1 = st.p2
      then { st with s1 := 0, p2 := 0, tw := 0 } else { st with s1 := 0, p2 := 0 }) := by
  by_cases h : st.s1 = st.p2
  · rw [if_pos h]
    exact seqAS (n := 131) rfl (ifeq_eq st h) (loop214 _)
  · rw [if_neg h]
    exact skip (p := dag219) (n := 131) rfl (ifeq_ne st h)

/-- The rotated next-candidate loop of Dag230 (nodes 136/300):
`np++; while s1 {s1--; np++}`. -/
theorem loop136 : ∀ (k : Nat) (st : AS), st.s1 = k →
    Rn (.node 136) st { st with np := st.np + k + 1, s1 := 0 } := by
  intro k
  induction k with
  | zero =>
      intro st h
      have hinc : Run dag219 (.inc 0) (enc st) .normal (enc { st with np := st.np + 1 }) := by
        have := Run.inc (p := dag219) 0 (enc st)
        rwa [show enc st 0 = st.np from rfl, upd_np] at this
      have hz : Run dag219 (.decnz 6) (enc { st with np := st.np + 1 }) (.brk 1)
          (enc { st with np := st.np + 1 }) := Run.decZero 6 _ (by simp [enc, h])
      have h300 : Run dag219 (.node 300) (enc { st with np := st.np + 1 }) .normal
          (enc { st with np := st.np + 1 }) := Run.carBrk1 300 _ _ hz
      have := Run.cdrNormal (p := dag219) 136 _ _ _ hinc h300
      have e : ({ st with np := st.np + 1 } : AS) = { st with np := st.np + 0 + 1, s1 := 0 } := by
        cases st; simp only at h; subst h; rfl
      rw [e] at this
      exact this
  | succ k ih =>
      intro st h
      have hinc : Run dag219 (.inc 0) (enc st) .normal (enc { st with np := st.np + 1 }) := by
        have := Run.inc (p := dag219) 0 (enc st)
        rwa [show enc st 0 = st.np from rfl, upd_np] at this
      have hdec : Run dag219 (.decnz 6) (enc { st with np := st.np + 1 }) .normal
          (enc { st with np := st.np + 1, s1 := k }) := by
        have := Run.decPos (p := dag219) 6 (enc { st with np := st.np + 1 }) k (by simp [enc, h])
        rwa [upd_s1] at this
      have h300 : Run dag219 (.node 300) (enc { st with np := st.np + 1 }) (.cont 1)
          (enc { st with np := st.np + 1, s1 := k }) :=
        Run.cdrContS 300 0 _ _ _ hdec (Run.contS 1 _)
      have hrest := ih { st with np := st.np + 1, s1 := k } rfl
      have := Run.cdrCont1 (p := dag219) 136 _ _ _ _ _ hinc h300 hrest
      have e2 : ({ ({ st with np := st.np + 1, s1 := k } : AS) with
          np := (({ st with np := st.np + 1, s1 := k } : AS)).np + k + 1, s1 := 0 } : AS) =
          { st with np := st.np + (k + 1) + 1, s1 := 0 } := by
        cases st; simp only; congr 1; omega
      rw [e2] at this
      exact this

/-! ## Fetch, MP and NIP -/

/-- The fetch (node 133): a nonzero proof list is decremented; an exhausted
one loads the next candidate. -/
theorem fetch_pos (st : AS) (v : Nat) (hv : st.pl = v + 1) : Rn (.node 133) st { st with pl := v } := by
  have hdec := Run.decPos (p := dag219) 8 (enc st) v (by simp [enc, hv])
  rw [upd_pl] at hdec
  have h134 := brk_cdr (p := dag219) (n := 134) (k := 0) rfl hdec (Run.brkS 0 _)
  exact skip (p := dag219) (n := 133) rfl h134

theorem fetch_zero (st : AS) (hpl : st.pl = 0) (h1 : st.s1 = 0) :
    Rn (.node 133) st { st with pl := st.np, np := st.np + 1 } := by
  have h134 : Rn (.node 134) st st :=
    skip (p := dag219) (n := 134) rfl (Run.decZero 8 (enc st) (by simp [enc, hpl]))
  have h135 := seqAS (n := 135) rfl (loop194 st)
    (loop136 _ _ rfl)
  have := seqAS (n := 133) rfl h134 h135
  apply rn_eq this
  cases st; simp only at hpl h1; subst hpl; subst h1; simp [updAS, enc]

/-- The MP branch (node 150). -/
theorem mp_branch (st : AS) (hc : Clean st) :
    Rn (.node 150) st (if wim st.tw st.p1 = st.p2
      then { st with tw := st.p1, ws := P 0 st.ws, p2 := 0 }
      else { st with tw := 0, p2 := 0 }) := by
  have := seqAS (n := 150) rfl (seqAS (n := 161) rfl (par1 st hc) (cons _ hc))
    (seqAS (n := 151) rfl (loop216 _) (ifeq_par1 _ hc.2))
  apply rn_eq this
  obtain ⟨h1, h2⟩ := hc
  cases st; simp only at h1 h2; subst h1; subst h2
  simp only [ofNat_P, Nat.zero_add]

/-- The NIP branch (node 152) when the cache is not the falsity code. -/
theorem nip_branch (st : AS) (hc : Clean st) (hh : st.p2 ≠ 1) :
    Rn (.node 152) st { st with p2 := (Cantor.ofNat st.ws).1, ws := (Cantor.ofNat st.ws).2 } := by
  have hinc := inc_AS 6 (by omega) st
  have hne : (updAS st 6 (enc st 6 + 1)).s1 ≠ (updAS st 6 (enc st 6 + 1)).p2 := by
    simp only [updAS, enc, hc.1]; omega
  have h132 := skip (p := dag219) (n := 132) rfl (ifeq_ne _ hne)
  have h153 := seqAS (n := 153) rfl h132 (pop_p2 _ ⟨rfl, hc.2⟩)
  have := seqAS (n := 152) rfl hinc h153
  apply rn_eq this
  obtain ⟨h1, h2⟩ := hc
  cases st; simp only at h1 h2; subst h1; subst h2; simp [updAS, enc]

/-- The NIP branch halts on the falsity code. -/
theorem nip_halt (st : AS) (hc : Clean st) (hh : st.p2 = 1) :
    ∃ R', Run dag219 (.node 152) (enc st) .halt R' := by
  have hinc := inc_AS 6 (by omega) st
  have heq : (updAS st 6 (enc st 6 + 1)).s1 = (updAS st 6 (enc st 6 + 1)).p2 := by
    simp only [updAS, enc, hc.1, hh]
  have h132 := halt_cdr (p := dag219) (n := 132) rfl (ifeq_eq _ heq) (Run.halt _)
  have h153 := halt_car (p := dag219) (n := 153) rfl h132
  exact ⟨_, halt_cdr (p := dag219) (n := 152) rfl hinc h153⟩

end SetTheory.BusyBeaver.ZFC.L2Q
