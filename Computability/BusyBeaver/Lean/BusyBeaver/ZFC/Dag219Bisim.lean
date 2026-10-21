import BusyBeaver.ZFC.Dag219
import BusyBeaver.ZFC.RMTransfer

/-!
`dag219` and `dag222` halt alike, from every register file.

The two programs differ only at the equality test, node 123. `dag222` decrements `s1`
(register 6) and `p2` (register 5) together (nodes 124-129, 199, 207); `dag219` runs Source
140's routine on the appended nodes 461-466. Both return normally iff the two registers agree,
otherwise break one level, and both leave them zero (`eq222`, `eq219`). Every other node below
461 is the same in both programs and points below 461, so a run of either program transfers
to the other (`run_transfer`), and so does iterating the root (`iter_iff`).

The separate `Dag219Equiv` facade supplies the legacy enumerator/seed endpoint.
This module depends only on the register programs and generic run transfer.
-/

namespace SetTheory.BusyBeaver.ZFC.Dag219

open RMDag

/-! ## Transfer of runs across one changed node -/

/-- The edge is a leaf or a node below `N`. -/
abbrev inside (N : Nat) : Edge → Bool := RMTransfer.inside (fun n => decide (n < N))

section transfer

variable {p q : Prog} {N n0 : Nat}
  (hpq : ∀ n < N, n ≠ n0 → p.nodes n = q.nodes n)
  (hc : ∀ n < N, n ≠ n0 → inside N (p.nodes n).1 = true ∧ inside N (p.nodes n).2 = true)
  (h0 : ∀ R x R', Run p (.node n0) R x R' → Run q (.node n0) R x R')
include hpq hc h0

private theorem closed : RMTransfer.Closed p q (fun n => decide (n < N)) :=
  RMTransfer.closed_of_contract (fun _ hn => of_decide_eq_true hn)
    (fun n hn _ hne => ⟨hpq n hn hne, hc n hn hne⟩) h0

/-- Runs transfer through the generic closed-set theorem. -/
theorem run_transfer {e : Edge} {R : Regs} {x : Exit} {R' : Regs} (h : Run p e R x R') :
    inside N e = true → Run q e R x R' :=
  RMTransfer.run_transfer (closed hpq hc h0) h

theorem iter_transfer (hroot : p.root = q.root) (hr : inside N (.node p.root) = true) {R : Regs}
    (h : IterHalts p R) : IterHalts q R :=
  RMTransfer.iter_transfer (closed hpq hc h0) hroot hr h

end transfer

/-! ## The two equality tests, on any register file

`setR R s p` is `R` with `s1 = s` and `p2 = p`. -/

section contracts

variable (R : Regs)

def setR (s p : Nat) : Regs := upd (upd R 6 s) 5 p

@[simp] theorem setR_6 (s p : Nat) : setR R s p 6 = s := by simp [setR, upd]
@[simp] theorem setR_5 (s p : Nat) : setR R s p 5 = p := by simp [setR, upd]

@[simp] theorem upd_setR_6 (s p v : Nat) : upd (setR R s p) 6 v = setR R v p := by
  funext i; simp only [setR, upd]; by_cases h6 : i = 6 <;> by_cases h5 : i = 5 <;> simp_all

@[simp] theorem upd_setR_5 (s p v : Nat) : upd (setR R s p) 5 v = setR R s v := by
  funext i; simp only [setR, upd]; by_cases h5 : i = 5 <;> simp_all

theorem setR_self : setR R (R 6) (R 5) = R := by
  funext i; simp only [setR, upd]; by_cases h6 : i = 6 <;> by_cases h5 : i = 5 <;> simp_all

theorem run_eq {p : Prog} {e : Edge} {R1 R2 R3 : Regs} {x : Exit} (h : Run p e R1 x R2)
    (he : R2 = R3) : Run p e R1 x R3 := he ▸ h

/-! ### dag219: `P = (D6, C2)` (461), `U = (P, B)` (462), `A = (D5, U)` (463), `L = (A, D6)` (464),
`Z = (D5, C1)` (465), `R = (Z, U)` (466), `E = (L, R)` (123). `A` cancels the counters, `L`
breaks exactly on equality, `R` clears both and breaks. -/

theorem eqU_pos (b p : Nat) : Run dag219 (.node 462) (setR R (b + 1) p) (.cont 1) (setR R b p) :=
  .carCont 462 0 _ _ (cont_cdr (p := dag219) (n := 461) (k := 0) rfl
    (by simpa using Run.decPos (p := dag219) 6 (setR R (b + 1) p) b (by simp)) (.contS 1 _))

theorem eqU_zero (p : Nat) : Run dag219 (.node 462) (setR R 0 p) (.brk 1) (setR R 0 p) :=
  brk_cdr (p := dag219) (n := 462) (k := 0) rfl
    (skip (p := dag219) (n := 461) rfl (.decZero 6 _ (by simp))) (.brkS 0 _)

/-- The cancellation loop `A`. -/
theorem eqA : ∀ a s : Nat,
    (a ≤ s → Run dag219 (.node 463) (setR R s a) .normal (setR R (s - a) 0)) ∧
    (s < a → Run dag219 (.node 463) (setR R s a) (.brk 1) (setR R 0 (a - s - 1)))
  | 0, s => ⟨fun _ => skip (p := dag219) (n := 463) rfl (.decZero 5 _ (by simp)),
      fun h => absurd h (Nat.not_lt_zero _)⟩
  | a + 1, s => by
      have hdec : Run dag219 (.decnz 5) (setR R s (a + 1)) .normal (setR R s a) := by
        simpa using Run.decPos (p := dag219) 5 (setR R s (a + 1)) a (by simp)
      rcases s with _ | b
      · exact ⟨fun h => by omega, fun _ => run_eq
          (brk_cdr (p := dag219) (n := 463) (k := 0) rfl hdec (eqU_zero R a)) (by simp)⟩
      · obtain ⟨ih1, ih2⟩ := eqA a b
        refine ⟨fun h => ?_, fun h => ?_⟩
        · exact run_eq (restart (p := dag219) (n := 463) rfl hdec (eqU_pos R b a) (ih1 (by omega)))
            (by congr 1; omega)
        · exact run_eq (restart (p := dag219) (n := 463) rfl hdec (eqU_pos R b a) (ih2 (by omega)))
            (by congr 1; omega)

theorem eqL_eq (s : Nat) : Run dag219 (.node 464) (setR R s s) (.brk 1) (setR R 0 0) :=
  brk_cdr (p := dag219) (n := 464) (k := 0) rfl
    (run_eq ((eqA R s s).1 (Nat.le_refl s)) (by simp)) (.decZero 6 _ (by simp))

theorem eqL_ne {s p : Nat} (h : s ≠ p) :
    ∃ x y, Run dag219 (.node 464) (setR R s p) .normal (setR R y x) := by
  rcases Nat.lt_or_gt_of_ne h with h' | h'
  · exact ⟨_, _, skip (p := dag219) (n := 464) rfl ((eqA R p s).2 h')⟩
  · obtain ⟨c, hc⟩ : ∃ c, s - p = c + 1 := ⟨s - p - 1, by omega⟩
    have hdec : Run dag219 (.decnz 6) (setR R (s - p) 0) .normal (setR R c 0) := by
      simpa using Run.decPos (p := dag219) 6 (setR R (s - p) 0) c (by simp [hc])
    exact ⟨0, c, seq (p := dag219) (n := 464) rfl ((eqA R p s).1 (by omega)) hdec⟩

/-- `Z` clears `p2`. -/
theorem eqZ : ∀ a s : Nat, Run dag219 (.node 465) (setR R s a) .normal (setR R s 0)
  | 0, s => skip (p := dag219) (n := 465) rfl (.decZero 5 _ (by simp))
  | a + 1, s => restart (p := dag219) (n := 465) rfl
      (by simpa using Run.decPos (p := dag219) 5 (setR R s (a + 1)) a (by simp)) (.contS 0 _)
      (eqZ a s)

/-- `R` clears `p2`, then `s1`, and breaks. -/
theorem eqR : ∀ b a : Nat, Run dag219 (.node 466) (setR R b a) (.brk 1) (setR R 0 0)
  | 0, a => brk_cdr (p := dag219) (n := 466) (k := 0) rfl (eqZ R a 0) (eqU_zero R 0)
  | b + 1, a => restart (p := dag219) (n := 466) rfl (eqZ R a (b + 1)) (eqU_pos R b 0) (eqR b 0)

theorem eq219' (s p : Nat) :
    Run dag219 (.node 123) (setR R s p) (if s = p then .normal else .brk 1) (setR R 0 0) := by
  by_cases h : s = p
  · subst h; simpa using skip (p := dag219) (n := 123) rfl (eqL_eq R s)
  · obtain ⟨x, y, hL⟩ := eqL_ne R h
    simpa [h] using brk_cdr (p := dag219) (n := 123) (k := 0) rfl hL (eqR R y x)

/-! ### dag222: the joint decrement loop 124, the transfer 207 and the clear 199. -/

def dist (a b : Nat) : Nat := if a ≤ b then b - a else a - b

theorem loop124 : ∀ s p : Nat,
    Run Dag222.dag222 (.node 124) (setR R s p) .normal (setR R 0 (dist s p))
  | 0, p => run_eq (skip (p := Dag222.dag222) (n := 124) rfl (.decZero 6 _ (by simp)))
      (by simp [dist])
  | s + 1, p => by
      have hdec : Run Dag222.dag222 (.decnz 6) (setR R (s + 1) p) .normal (setR R s p) := by
        simpa using Run.decPos (p := Dag222.dag222) 6 (setR R (s + 1) p) s (by simp)
      rcases p with _ | b
      · have h207 := transfer (p := Dag222.dag222) (n := 207) (m := 191) (src := 6) (dst := 5)
          rfl rfl (by decide) (setR R s 0)
        simp only [setR_5, setR_6, upd_setR_5, upd_setR_6, Nat.zero_add] at h207
        have h127 := seq (p := Dag222.dag222) (n := 127) rfl h207 (.inc 5 _)
        simp only [setR_5, upd_setR_5] at h127
        have h125 := seq (p := Dag222.dag222) (n := 125) rfl
          (skip (p := Dag222.dag222) (n := 126) rfl (.decZero 5 _ (by simp))) h127
        exact run_eq (seq (p := Dag222.dag222) (n := 124) rfl hdec h125) (by simp [dist])
      · have h126 := cont_cdr (p := Dag222.dag222) (n := 126) (k := 0) rfl
          (by simpa using Run.decPos (p := Dag222.dag222) 5 (setR R s (b + 1)) b (by simp))
          (.contS 1 _)
        exact run_eq (restart (p := Dag222.dag222) (n := 124) rfl hdec
          (.carCont 125 0 _ _ h126) (loop124 s b)) (by congr 1; simp only [dist]; split <;> split <;> omega)

theorem eq222' (s p : Nat) : Run Dag222.dag222 (.node 123) (setR R s p)
    (if s = p then .normal else .brk 1) (setR R 0 0) := by
  have h124 := loop124 R s p
  by_cases h : s = p
  · subst h
    simpa [dist] using seq (p := Dag222.dag222) (n := 123) rfl h124
      (skip (p := Dag222.dag222) (n := 128) rfl (.decZero 5 _ (by simp [dist])))
  · obtain ⟨c, hc⟩ : ∃ c, dist s p = c + 1 := ⟨dist s p - 1, by simp only [dist]; split <;> omega⟩
    have hdec : Run Dag222.dag222 (.decnz 5) (setR R 0 (dist s p)) .normal (setR R 0 c) := by
      simpa using Run.decPos (p := Dag222.dag222) 5 (setR R 0 (dist s p)) c (by simp [hc])
    have h199 := clear (p := Dag222.dag222) (n := 199) (r := 5) rfl (setR R 0 c)
    simp only [upd_setR_5] at h199
    have h129 := brk_cdr (p := Dag222.dag222) (n := 129) (k := 0) rfl h199 (.brkS 0 _)
    have h128 := brk_cdr (p := Dag222.dag222) (n := 128) (k := 0) rfl hdec h129
    simpa [h] using brk_cdr (p := Dag222.dag222) (n := 123) (k := 0) rfl h124 h128

/-- The exit of both equality tests. -/
def eqExit (R : Regs) : Exit := if R 6 = R 5 then .normal else .brk 1

theorem eq219 : Run dag219 (.node 123) R (eqExit R) (setR R 0 0) := by
  have := eq219' R (R 6) (R 5); rw [setR_self] at this; exact this

theorem eq222 : Run Dag222.dag222 (.node 123) R (eqExit R) (setR R 0 0) := by
  have := eq222' R (R 6) (R 5); rw [setR_self] at this; exact this

end contracts

/-! ## The equivalence -/

theorem agree (n : Nat) (h : n < 461) (hn : n ≠ 123) : Dag222.dag222.nodes n = dag219.nodes n := by
  show _ = (eqNodes n).getD _
  rw [show eqNodes n = none by unfold eqNodes; split <;> first | rfl | omega]
  rfl

theorem inside222 : ∀ n < 461, n ≠ 123 →
    inside 461 (Dag222.dag222.nodes n).1 = true ∧ inside 461 (Dag222.dag222.nodes n).2 = true := by
  decide +kernel

theorem inside219 (n : Nat) (h : n < 461) (hn : n ≠ 123) :
    inside 461 (dag219.nodes n).1 = true ∧ inside 461 (dag219.nodes n).2 = true :=
  agree n h hn ▸ inside222 n h hn

/-- **`dag219` and `dag222` halt alike**, from every register file. -/
theorem iter_iff (R : Regs) : IterHalts dag219 R ↔ IterHalts Dag222.dag222 R :=
  ⟨iter_transfer (fun n h hn => (agree n h hn).symm) inside219
      (fun R x R' h => by obtain ⟨rfl, rfl⟩ := run_det h (eq219 R); exact eq222 R) rfl rfl,
   iter_transfer agree inside222
      (fun R x R' h => by obtain ⟨rfl, rfl⟩ := run_det h (eq222 R); exact eq219 R) rfl rfl⟩

end SetTheory.BusyBeaver.ZFC.Dag219
