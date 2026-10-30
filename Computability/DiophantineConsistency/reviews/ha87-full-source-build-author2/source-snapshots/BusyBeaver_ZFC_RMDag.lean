/-!
Register programs in the form produced by Andrew James Wade's TMBuilder.

A program is a DAG of cons cells: node `n` has a *car* edge and a *cdr*
edge. Leaves are register increments, `decnz` (decrement if nonzero,
otherwise break one level), `break k`, `continue k` and `halt`. Running a
node runs its car and then its cdr; a cdr finishing with `continue 1`
restarts the node, which is how loops are expressed.

This is the structured big-step semantics of the published verification
(upstream `ZF/m254/coq/tm/RM.v`), stated independently. The Turing machine
itself implements an equivalent path semantics; that equivalence belongs to
the TM layer. Here we prove determinism and the generic sequencing and loop
rules used by the program-level proofs.
-/

namespace SetTheory.BusyBeaver.ZFC.RMDag

inductive Edge where
  | node (n : Nat)
  | inc (r : Nat)
  | decnz (r : Nat)
  | brk (k : Nat)
  | cont (k : Nat)
  | halt
  deriving DecidableEq, Repr

structure Prog where
  nodes : Nat → Edge × Edge
  root : Nat

abbrev Regs := Nat → Nat

def upd (R : Regs) (r v : Nat) : Regs := fun i => if i = r then v else R i

@[simp] theorem upd_same (R : Regs) (r v : Nat) : upd R r v r = v := by simp [upd]

theorem upd_other (R : Regs) {r i : Nat} (v : Nat) (h : i ≠ r) : upd R r v i = R i := by
  simp [upd, h]

inductive Exit where
  | normal
  | brk (k : Nat)
  | cont (k : Nat)
  | halt
  deriving DecidableEq, Repr

/-- Structured big-step semantics; `brk k` and `cont k` exits carry `k ≥ 1`. -/
inductive Run (p : Prog) : Edge → Regs → Exit → Regs → Prop
  | inc (r : Nat) (R : Regs) : Run p (.inc r) R .normal (upd R r (R r + 1))
  | decPos (r : Nat) (R : Regs) (v : Nat) (h : R r = v + 1) : Run p (.decnz r) R .normal (upd R r v)
  | decZero (r : Nat) (R : Regs) (h : R r = 0) : Run p (.decnz r) R (.brk 1) R
  | brk0 (R : Regs) : Run p (.brk 0) R .normal R
  | brkS (k : Nat) (R : Regs) : Run p (.brk (k + 1)) R (.brk (k + 1)) R
  | contS (k : Nat) (R : Regs) : Run p (.cont (k + 1)) R (.cont (k + 1)) R
  | halt (R : Regs) : Run p .halt R .halt R
  | carBrk1 (n : Nat) (R R' : Regs) :
      Run p (p.nodes n).1 R (.brk 1) R' → Run p (.node n) R .normal R'
  | carBrkS (n k : Nat) (R R' : Regs) :
      Run p (p.nodes n).1 R (.brk (k + 2)) R' → Run p (.node n) R (.brk (k + 1)) R'
  | carCont (n k : Nat) (R R' : Regs) :
      Run p (p.nodes n).1 R (.cont (k + 1)) R' → Run p (.node n) R (.cont (k + 1)) R'
  | carHalt (n : Nat) (R R' : Regs) :
      Run p (p.nodes n).1 R .halt R' → Run p (.node n) R .halt R'
  | cdrNormal (n : Nat) (R R1 R' : Regs) :
      Run p (p.nodes n).1 R .normal R1 → Run p (p.nodes n).2 R1 .normal R' →
      Run p (.node n) R .normal R'
  | cdrBrk (n k : Nat) (R R1 R' : Regs) :
      Run p (p.nodes n).1 R .normal R1 → Run p (p.nodes n).2 R1 (.brk (k + 1)) R' →
      Run p (.node n) R (.brk (k + 1)) R'
  | cdrCont1 (n : Nat) (R R1 R2 R' : Regs) (x : Exit) :
      Run p (p.nodes n).1 R .normal R1 → Run p (p.nodes n).2 R1 (.cont 1) R2 →
      Run p (.node n) R2 x R' → Run p (.node n) R x R'
  | cdrContS (n k : Nat) (R R1 R' : Regs) :
      Run p (p.nodes n).1 R .normal R1 → Run p (p.nodes n).2 R1 (.cont (k + 2)) R' →
      Run p (.node n) R (.cont (k + 1)) R'
  | cdrHalt (n : Nat) (R R1 R' : Regs) :
      Run p (p.nodes n).1 R .normal R1 → Run p (p.nodes n).2 R1 .halt R' →
      Run p (.node n) R .halt R'

/-- Iterating the root: the instruction pointer overflows at the end of the
root and restarts it. -/
inductive IterHalts (p : Prog) : Regs → Prop
  | halt (R R' : Regs) : Run p (.node p.root) R .halt R' → IterHalts p R
  | next (R R' : Regs) : Run p (.node p.root) R .normal R' → IterHalts p R' → IterHalts p R

/-! ## Determinism -/

/-- Align the car results, then the cdr results, then any restarted run. -/
theorem run_det {p : Prog} {e : Edge} {R : Regs} {x : Exit} {R' : Regs}
    (h : Run p e R x R') : ∀ {y : Exit} {R'' : Regs}, Run p e R y R'' → x = y ∧ R' = R'' := by
  induction h with
  | inc | brk0 | brkS | contS | halt => intro y R'' h2; cases h2; exact ⟨rfl, rfl⟩
  | decPos r R v hv =>
      intro y R'' h2
      cases h2 with
      | decPos _ _ v' hv' => rw [hv] at hv'; cases hv'; exact ⟨rfl, rfl⟩
      | decZero _ _ hz => rw [hv] at hz; cases hz
  | decZero r R hz =>
      intro y R'' h2
      cases h2 with
      | decPos _ _ v' hv' => rw [hz] at hv'; cases hv'
      | decZero => exact ⟨rfl, rfl⟩
  -- A non-normal car fixes the whole node result.
  | carBrk1 _ _ _ _ ih
  | carBrkS _ _ _ _ _ ih
  | carCont _ _ _ _ _ ih
  | carHalt _ _ _ _ ih =>
      intro y R'' h2
      cases h2 <;> first
      | rename_i h'
        obtain ⟨he, hR⟩ := ih h'
        cases he <;> cases hR <;> exact ⟨rfl, rfl⟩
      | rename_i h' h''
        cases (ih h').1
      | rename_i h' h'' h'''
        cases (ih h').1
  -- A normal car fixes the intermediate registers before the cdr is compared.
  | cdrNormal _ _ _ _ _ _ ih1 ih2
  | cdrBrk _ _ _ _ _ _ _ ih1 ih2
  | cdrContS _ _ _ _ _ _ _ ih1 ih2
  | cdrHalt _ _ _ _ _ _ ih1 ih2 =>
      intro y R'' h3
      cases h3 with
      | cdrCont1 _ _ _ _ _ _ h' h'' _ =>
          rw [← (ih1 h').2] at h''
          cases (ih2 h'').1
      | _ => first
        | rename_i h'
          cases (ih1 h').1
        | rename_i h' h''
          obtain ⟨he, hR⟩ := ih1 h'
          cases he
          cases hR
          obtain ⟨he, hR⟩ := ih2 h''
          cases he <;> cases hR <;> exact ⟨rfl, rfl⟩
  | cdrCont1 n R R1 R2 R' x h1 h2 h3 ih1 ih2 ih3 =>
      intro y R'' h4
      cases h4 with
      | cdrCont1 _ _ _ _ _ _ h' h'' h''' =>
          rw [← (ih1 h').2] at h''
          rw [← (ih2 h'').2] at h'''
          exact ih3 h'''
      | _ => first
        | rename_i h'
          cases (ih1 h').1
        | rename_i h' h''
          rw [← (ih1 h').2] at h''
          cases (ih2 h'').1

/-! ## Composition rules -/

variable {p : Prog}

/-- Sequencing: both halves finish normally. -/
theorem seq {n : Nat} {a b : Edge} (hn : p.nodes n = (a, b)) {R R1 R2 : Regs}
    (ha : Run p a R .normal R1) (hb : Run p b R1 .normal R2) : Run p (.node n) R .normal R2 :=
  .cdrNormal n R R1 R2 (by rwa [hn]) (by rwa [hn])

/-- A car that breaks one level skips the cdr. -/
theorem skip {n : Nat} {a b : Edge} (hn : p.nodes n = (a, b)) {R R1 : Regs}
    (ha : Run p a R (.brk 1) R1) : Run p (.node n) R .normal R1 :=
  .carBrk1 n R R1 (by rwa [hn])

/-- Halting in the car. -/
theorem halt_car {n : Nat} {a b : Edge} (hn : p.nodes n = (a, b)) {R R1 : Regs}
    (ha : Run p a R .halt R1) : Run p (.node n) R .halt R1 :=
  .carHalt n R R1 (by rwa [hn])

/-- Halting in the cdr. -/
theorem halt_cdr {n : Nat} {a b : Edge} (hn : p.nodes n = (a, b)) {R R1 R2 : Regs}
    (ha : Run p a R .normal R1) (hb : Run p b R1 .halt R2) : Run p (.node n) R .halt R2 :=
  .cdrHalt n R R1 R2 (by rwa [hn]) (by rwa [hn])

/-- A cdr breaking `k+1` levels breaks the node `k+1` levels, except that one level is consumed
when the node is the target of the break. -/
theorem brk_cdr {n k : Nat} {a b : Edge} (hn : p.nodes n = (a, b)) {R R1 R2 : Regs}
    (ha : Run p a R .normal R1) (hb : Run p b R1 (.brk (k + 1)) R2) :
    Run p (.node n) R (.brk (k + 1)) R2 :=
  .cdrBrk n k R R1 R2 (by rwa [hn]) (by rwa [hn])

/-- A car breaking `k+2` levels breaks the node `k+1` levels. -/
theorem brk_car {n k : Nat} {a b : Edge} (hn : p.nodes n = (a, b)) {R R1 : Regs}
    (ha : Run p a R (.brk (k + 2)) R1) : Run p (.node n) R (.brk (k + 1)) R1 :=
  .carBrkS n k R R1 (by rwa [hn])

/-- A cdr continuing `k+2` levels continues the node `k+1` levels. -/
theorem cont_cdr {n k : Nat} {a b : Edge} (hn : p.nodes n = (a, b)) {R R1 R2 : Regs}
    (ha : Run p a R .normal R1) (hb : Run p b R1 (.cont (k + 2)) R2) :
    Run p (.node n) R (.cont (k + 1)) R2 :=
  .cdrContS n k R R1 R2 (by rwa [hn]) (by rwa [hn])

/-- A cdr continuing one level restarts the node. -/
theorem restart {n : Nat} {a b : Edge} (hn : p.nodes n = (a, b)) {R R1 R2 R' : Regs} {x : Exit}
    (ha : Run p a R .normal R1) (hb : Run p b R1 (.cont 1) R2)
    (hrest : Run p (.node n) R2 x R') : Run p (.node n) R x R' :=
  .cdrCont1 n R R1 R2 R' x (by rwa [hn]) (by rwa [hn]) hrest

/-! ## Loops -/

/-- The generic `while r > 0: r -= 1; body` loop. `body` finishes with
`continue 1` and leaves the counter unchanged. -/
def loopRes (g : Regs → Regs) (r : Nat) : Nat → Regs → Regs
  | 0, R => R
  | k + 1, R => loopRes g r k (g (upd R r k))

theorem while_loop {n r : Nat} {b : Edge} (hn : p.nodes n = (.decnz r, b)) (g : Regs → Regs)
    (hg : ∀ R, g R r = R r) (hbody : ∀ R, Run p b R (.cont 1) (g R)) :
    ∀ (k : Nat) (R : Regs), R r = k → Run p (.node n) R .normal (loopRes g r k R)
  | 0, R, hk => skip hn (.decZero r R hk)
  | k + 1, R, hk => by
      apply restart hn (.decPos r R k hk) (hbody _)
      apply while_loop hn g hg hbody k
      rw [hg]; simp

theorem upd_comm (R : Regs) {a b : Nat} (h : a ≠ b) (x y : Nat) :
    upd (upd R a x) b y = upd (upd R b y) a x := by
  funext i; simp only [upd]; by_cases ha : i = a <;> by_cases hb : i = b <;> simp_all

theorem upd_upd (R : Regs) (a x y : Nat) : upd (upd R a x) a y = upd R a y := by
  funext i; simp only [upd]; by_cases ha : i = a <;> simp [ha]

theorem upd_self (R : Regs) (a : Nat) : upd R a (R a) = R := by
  funext i; simp only [upd]; by_cases ha : i = a <;> simp [ha]

/-- A loop body `(inc dst, continue 2)` behind one node: transfer `src` into `dst`. -/
theorem transfer {n m src dst : Nat} (hn : p.nodes n = (.decnz src, .node m))
    (hm : p.nodes m = (.inc dst, .cont 2)) (hsd : src ≠ dst) :
    ∀ R : Regs, Run p (.node n) R .normal (upd (upd R dst (R dst + R src)) src 0) := by
  intro R
  have hbody : ∀ R, Run p (.node m) R (.cont 1) (upd R dst (R dst + 1)) := fun R =>
    cont_cdr hm (.inc dst R) (.contS 1 _)
  have h := while_loop hn (fun R => upd R dst (R dst + 1)) (fun R => upd_other R _ hsd) hbody
    (R src) R rfl
  suffices e : ∀ k R, R src = k → loopRes (fun R => upd R dst (R dst + 1)) src k R =
      upd (upd R dst (R dst + k)) src 0 by rwa [e (R src) R rfl] at h
  intro k
  induction k with
  | zero =>
      intro R hR; simp only [loopRes, Nat.add_zero]
      rw [upd_self, ← hR, upd_self]
  | succ k ih =>
      intro R hR
      simp only [loopRes]
      rw [ih _ (by simp [upd_other _ _ hsd])]
      funext i
      simp only [upd]
      by_cases h1 : i = src <;> by_cases h2 : i = dst <;> simp_all <;> omega

/-- A loop body `((inc d₁, inc d₂), continue 2)`: copy `src` into two registers. -/
theorem copy2 {n m m' src d1 d2 : Nat} (hn : p.nodes n = (.decnz src, .node m))
    (hm : p.nodes m = (.node m', .cont 2)) (hm' : p.nodes m' = (.inc d1, .inc d2))
    (h1 : src ≠ d1) (h2 : src ≠ d2) (h12 : d1 ≠ d2) :
    ∀ R : Regs, Run p (.node n) R .normal
      (upd (upd (upd R d1 (R d1 + R src)) d2 (R d2 + R src)) src 0) := by
  intro R
  let g : Regs → Regs := fun R => upd (upd R d1 (R d1 + 1)) d2 (R d2 + 1)
  have hbody : ∀ R, Run p (.node m) R (.cont 1) (g R) := by
    intro R
    have hin : Run p (.node m') R .normal (upd (upd R d1 (R d1 + 1)) d2 (R d2 + 1)) := by
      have := seq hm' (.inc d1 R) (.inc d2 (upd R d1 (R d1 + 1)))
      rwa [upd_other R _ (Ne.symm h12)] at this
    exact cont_cdr hm hin (.contS 1 _)
  have hg : ∀ R, g R src = R src := by
    intro R; simp only [g]; rw [upd_other _ _ h2, upd_other _ _ h1]
  have h := while_loop hn g hg hbody (R src) R rfl
  suffices e : ∀ k R, R src = k → loopRes g src k R =
      upd (upd (upd R d1 (R d1 + k)) d2 (R d2 + k)) src 0 by rwa [e (R src) R rfl] at h
  intro k
  induction k with
  | zero =>
      intro R hR; simp only [loopRes, Nat.add_zero]
      rw [upd_self, upd_self, ← hR, upd_self]
  | succ k ih =>
      intro R hR
      simp only [loopRes]
      rw [ih _ (by simp only [g]; rw [upd_other _ _ h2, upd_other _ _ h1]; simp)]
      funext i
      simp only [g, upd]
      by_cases ha : i = src <;> by_cases hb : i = d1 <;> by_cases hc : i = d2 <;> simp_all <;> omega

/-- A loop `(decnz r, continue 1)` clears `r`. -/
theorem clear {n r : Nat} (hn : p.nodes n = (.decnz r, .cont 1)) :
    ∀ R : Regs, Run p (.node n) R .normal (upd R r 0) := by
  intro R
  have h := while_loop hn (fun R => R) (fun _ => rfl) (fun R => .contS 0 R) (R r) R rfl
  suffices e : ∀ k R, R r = k → loopRes (fun R => R) r k R = upd R r 0 by rwa [e (R r) R rfl] at h
  intro k
  induction k with
  | zero => intro R hR; simp only [loopRes]; rw [← hR, upd_self]
  | succ k ih =>
      intro R hR
      simp only [loopRes]
      rw [ih _ (by simp), upd_upd]

end SetTheory.BusyBeaver.ZFC.RMDag
