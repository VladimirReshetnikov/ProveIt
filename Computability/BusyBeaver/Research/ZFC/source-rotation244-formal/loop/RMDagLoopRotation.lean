import BusyBeaver.ZFC.RMDag

/-!
A transfer loop followed by one increment and its rotated form have the same
complete register-file normal form. Only the displayed local row equations
are assumed. These structured-semantic lemmas do not assert a concrete program,
a path-semantics bridge, a binary-machine calibration, or an internal PA theorem.
-/
set_option autoImplicit false

namespace SetTheory.BusyBeaver.ZFC.RMDagLoopRotation
open RMDag

/-- Transfer every unit of `src` into `dst`, then increment `dst` once more. -/
def normalFile (R : Regs) (src dst : Nat) : Regs :=
  upd (upd R dst (R dst + R src + 1)) src 0

theorem normalFile_src (R : Regs) (src dst : Nat) :
    normalFile R src dst src = 0 := by
  simp only [normalFile, upd_same]

theorem normalFile_dst (R : Regs) {src dst : Nat} (hsd : src ≠ dst) :
    normalFile R src dst dst = R dst + R src + 1 := by
  simp only [normalFile, upd_other _ _ (Ne.symm hsd), upd_same]

theorem normalFile_other (R : Regs) {src dst i : Nat}
    (his : i ≠ src) (hid : i ≠ dst) : normalFile R src dst i = R i := by
  simp only [normalFile, upd_other _ _ his, upd_other _ _ hid]

/-- The original three-node arrangement: decrement/transfer, then increment. -/
theorem old_normal {p : Prog} {n l b src dst : Nat}
    (hn : p.nodes n = (.node l, .inc dst))
    (hl : p.nodes l = (.decnz src, .node b))
    (hb : p.nodes b = (.inc dst, .cont 2)) (hsd : src ≠ dst) (R : Regs) :
    Run p (.node n) R .normal (normalFile R src dst) := by
  have h := seq hn (transfer hl hb hsd R)
    (.inc dst (upd (upd R dst (R dst + R src)) src 0))
  have he :
      upd (upd (upd R dst (R dst + R src)) src 0) dst
        (upd (upd R dst (R dst + R src)) src 0 dst + 1) =
      normalFile R src dst := by
    funext i
    by_cases his : i = src <;> by_cases hid : i = dst <;>
      simp_all [normalFile, upd]
  rw [he] at h
  exact h

/-- The rotated two-node arrangement: increment before testing the counter. -/
theorem new_normal {p : Prog} {n l src dst : Nat}
    (hn : p.nodes n = (.inc dst, .node l))
    (hl : p.nodes l = (.decnz src, .cont 2)) (hsd : src ≠ dst) (R : Regs) :
    Run p (.node n) R .normal (normalFile R src dst) := by
  suffices h : ∀ k R, R src = k →
      Run p (.node n) R .normal (normalFile R src dst) from h (R src) R rfl
  intro k
  induction k with
  | zero =>
      intro R hR
      have hz : upd R dst (R dst + 1) src = 0 := by
        rw [upd_other R _ hsd, hR]
      have h := seq hn (.inc dst R) (skip hl (.decZero src _ hz))
      have he : upd R dst (R dst + 1) = normalFile R src dst := by
        funext i
        by_cases his : i = src <;> by_cases hid : i = dst <;>
          simp_all [normalFile, upd]
      rw [he] at h
      exact h
  | succ k ih =>
      intro R hR
      have hp : upd R dst (R dst + 1) src = k + 1 := by
        rw [upd_other R _ hsd, hR]
      have htest : Run p (.node l) (upd R dst (R dst + 1)) (.cont 1)
          (upd (upd R dst (R dst + 1)) src k) :=
        cont_cdr hl (.decPos src _ k hp) (.contS 1 _)
      have hrest := ih (upd (upd R dst (R dst + 1)) src k) (by simp only [upd_same])
      have h := restart hn (.inc dst R) htest hrest
      have he : normalFile (upd (upd R dst (R dst + 1)) src k) src dst =
          normalFile R src dst := by
        funext i
        by_cases his : i = src <;> by_cases hid : i = dst <;>
          simp_all [normalFile, upd] <;> omega
      rw [he] at h
      exact h

/-- Determinism transfers every exit/output judgment at the two local entries. -/
theorem run_iff {p q : Prog} {n l b n' l' src dst : Nat}
    (hn : p.nodes n = (.node l, .inc dst))
    (hl : p.nodes l = (.decnz src, .node b))
    (hb : p.nodes b = (.inc dst, .cont 2))
    (hn' : q.nodes n' = (.inc dst, .node l'))
    (hl' : q.nodes l' = (.decnz src, .cont 2)) (hsd : src ≠ dst)
    (R R' : Regs) (x : Exit) :
    Run p (.node n) R x R' ↔ Run q (.node n') R x R' := by
  constructor
  · intro h
    obtain ⟨hx, hR⟩ := run_det h (old_normal hn hl hb hsd R)
    rw [hx, hR]
    exact new_normal hn' hl' hsd R
  · intro h
    obtain ⟨hx, hR⟩ := run_det h (new_normal hn' hl' hsd R)
    rw [hx, hR]
    exact old_normal hn hl hb hsd R

end SetTheory.BusyBeaver.ZFC.RMDagLoopRotation
