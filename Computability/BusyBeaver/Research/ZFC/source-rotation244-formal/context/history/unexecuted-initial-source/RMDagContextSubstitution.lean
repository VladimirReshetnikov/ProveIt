import BusyBeaver.ZFC.RMDag

/-!
Substitute an equivalent structured macro at one node. Other admitted nodes
have identical rows and admitted children. Induction is on the complete Run
derivation, including the recursive restart premise; no acyclic-index argument
or finite-run bound is used. Concrete row/safety/WF/path obligations are separate.
-/
set_option autoImplicit false
namespace SetTheory.BusyBeaver.ZFC.RMDagContextSubstitution
open RMDag

structure Replacement (p q : Prog) (safe : Edge → Prop) (entry : Nat) : Prop where
  local_equiv : ∀ R R' x,
    Run p (.node entry) R x R' ↔ Run q (.node entry) R x R'
  rows : ∀ n, safe (.node n) → n ≠ entry → p.nodes n = q.nodes n
  children : ∀ n, safe (.node n) → n ≠ entry →
    safe (p.nodes n).1 ∧ safe (p.nodes n).2

theorem Replacement.symm {p q : Prog} {safe : Edge → Prop} {entry : Nat}
    (rep : Replacement p q safe entry) : Replacement q p safe entry := by
  constructor
  · intro R R' x
    exact (rep.local_equiv R R' x).symm
  · intro n hs hn
    exact (rep.rows n hs hn).symm
  · intro n hs hn
    rw [← rep.rows n hs hn]
    exact rep.children n hs hn

private theorem node_case {p q : Prog} {safe : Edge → Prop} {entry n : Nat}
    (rep : Replacement p q safe entry) {R R' : Regs} {x : Exit}
    (h : Run p (.node n) R x R') (hs : safe (.node n))
    (other : n ≠ entry → Run q (.node n) R x R') : Run q (.node n) R x R' := by
  by_cases hn : n = entry
  · subst n
    exact (rep.local_equiv R R' x).mp h
  · exact other hn

/-- Transfer every complete exit/output judgment from an admitted edge. -/
theorem forward {p q : Prog} {safe : Edge → Prop} {entry : Nat}
    (rep : Replacement p q safe entry) {e : Edge} {R R' : Regs} {x : Exit}
    (h : Run p e R x R') : safe e → Run q e R x R' := by
  induction h with
  | inc r R => intro _; exact .inc r R
  | decPos r R v hv => intro _; exact .decPos r R v hv
  | decZero r R hz => intro _; exact .decZero r R hz
  | brk0 R => intro _; exact .brk0 R
  | brkS k R => intro _; exact .brkS k R
  | contS k R => intro _; exact .contS k R
  | halt R => intro _; exact .halt R
  | carBrk1 n R R' h ih =>
      intro hs
      apply node_case rep (.carBrk1 n R R' h) hs
      intro hn
      apply Run.carBrk1 n R R'
      rw [← rep.rows n hs hn]
      exact ih (rep.children n hs hn).1
  | carBrkS n k R R' h ih =>
      intro hs
      apply node_case rep (.carBrkS n k R R' h) hs
      intro hn
      apply Run.carBrkS n k R R'
      rw [← rep.rows n hs hn]
      exact ih (rep.children n hs hn).1
  | carCont n k R R' h ih =>
      intro hs
      apply node_case rep (.carCont n k R R' h) hs
      intro hn
      apply Run.carCont n k R R'
      rw [← rep.rows n hs hn]
      exact ih (rep.children n hs hn).1
  | carHalt n R R' h ih =>
      intro hs
      apply node_case rep (.carHalt n R R' h) hs
      intro hn
      apply Run.carHalt n R R'
      rw [← rep.rows n hs hn]
      exact ih (rep.children n hs hn).1
  | cdrNormal n R R1 R' h1 h2 ih1 ih2 =>
      intro hs
      apply node_case rep (.cdrNormal n R R1 R' h1 h2) hs
      intro hn
      apply Run.cdrNormal n R R1 R'
      · rw [← rep.rows n hs hn]
        exact ih1 (rep.children n hs hn).1
      · rw [← rep.rows n hs hn]
        exact ih2 (rep.children n hs hn).2
  | cdrBrk n k R R1 R' h1 h2 ih1 ih2 =>
      intro hs
      apply node_case rep (.cdrBrk n k R R1 R' h1 h2) hs
      intro hn
      apply Run.cdrBrk n k R R1 R'
      · rw [← rep.rows n hs hn]
        exact ih1 (rep.children n hs hn).1
      · rw [← rep.rows n hs hn]
        exact ih2 (rep.children n hs hn).2
  | cdrCont1 n R R1 R2 R' x h1 h2 h3 ih1 ih2 ih3 =>
      intro hs
      apply node_case rep (.cdrCont1 n R R1 R2 R' x h1 h2 h3) hs
      intro hn
      apply Run.cdrCont1 n R R1 R2 R' x
      · rw [← rep.rows n hs hn]
        exact ih1 (rep.children n hs hn).1
      · rw [← rep.rows n hs hn]
        exact ih2 (rep.children n hs hn).2
      · exact ih3 hs
  | cdrContS n k R R1 R' h1 h2 ih1 ih2 =>
      intro hs
      apply node_case rep (.cdrContS n k R R1 R' h1 h2) hs
      intro hn
      apply Run.cdrContS n k R R1 R'
      · rw [← rep.rows n hs hn]
        exact ih1 (rep.children n hs hn).1
      · rw [← rep.rows n hs hn]
        exact ih2 (rep.children n hs hn).2
  | cdrHalt n R R1 R' h1 h2 ih1 ih2 =>
      intro hs
      apply node_case rep (.cdrHalt n R R1 R' h1 h2) hs
      intro hn
      apply Run.cdrHalt n R R1 R'
      · rw [← rep.rows n hs hn]
        exact ih1 (rep.children n hs hn).1
      · rw [← rep.rows n hs hn]
        exact ih2 (rep.children n hs hn).2

/-- Admitted entries have identical exits and complete register-file outputs. -/
theorem run_iff {p q : Prog} {safe : Edge → Prop} {entry : Nat}
    (rep : Replacement p q safe entry) {e : Edge} (hs : safe e)
    (R R' : Regs) (x : Exit) : Run p e R x R' ↔ Run q e R x R' :=
  ⟨fun h => forward rep h hs, fun h => forward rep.symm h hs⟩

theorem iter_forward {p q : Prog} {safe : Edge → Prop} {entry : Nat}
    (rep : Replacement p q safe entry) (hroot : p.root = q.root)
    (hs : safe (.node p.root)) {R : Regs} (h : IterHalts p R) : IterHalts q R := by
  induction h with
  | halt R R' h =>
      apply IterHalts.halt R R'
      rw [← hroot]
      exact forward rep h hs
  | next R R' h hrest ih =>
      apply IterHalts.next R R' _ ih
      rw [← hroot]
      exact forward rep h hs

/-- The whole root iteration preserves halting, with root safety explicit. -/
theorem iterHalts_iff {p q : Prog} {safe : Edge → Prop} {entry : Nat}
    (rep : Replacement p q safe entry) (hroot : p.root = q.root)
    (hs : safe (.node p.root)) (R : Regs) : IterHalts p R ↔ IterHalts q R := by
  constructor
  · exact iter_forward rep hroot hs
  · exact iter_forward rep.symm hroot.symm (by rw [← hroot]; exact hs)

end SetTheory.BusyBeaver.ZFC.RMDagContextSubstitution
