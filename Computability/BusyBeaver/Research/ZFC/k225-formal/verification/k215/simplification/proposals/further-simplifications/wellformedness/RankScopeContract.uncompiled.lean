import BusyBeaver.ZFC.RMEquiv

/-!
Research draft, NOT COMPILED. This is only the small abstract interface from
a certified topological fold to the existing WF proposition. It does not
implement the fold or claim its soundness. No placeholders or new axioms.

The proposed fold establishes `legal`, `rankEdge`, `breakEq`,
and `continueEq` by an invariant, rather than supplying their concrete
tables as new untrusted certificates and rechecking all the inequalities.
It may check the one scalar `rankRoot` condition at acceptance, avoiding
an initial generic termination/cardinality proof.
-/

namespace SetTheory.BusyBeaver.ZFC.RMEquiv

open RMDag

theorem wf_of_completion_rank_and_scopes
    (p : Prog) (nn : Nat) (rank B C : Nat → Nat)
    (rootBound : p.root < nn)
    (legal : ∀ n b, n < nn → edgeOk nn (child p n b))
    (rankRoot : rank p.root ≤ nn)
    (rankEdge : ∀ n b m, n < nn → child p n b = .node m → rank m < rank n)
    (breakEq : ∀ n, n < nn →
      B n = max (bE B (p.nodes n).1 - 1) (bE B (p.nodes n).2))
    (continueEq : ∀ n, n < nn →
      C n = max (cE C (p.nodes n).1) (cE C (p.nodes n).2 - 1))
    (breakRoot : B p.root = 0) (continueRoot : C p.root = 0) : WF p nn := by
  refine ⟨rootBound, legal, ⟨fun n => rank n + 1, ?_, ?_⟩,
    ⟨B, C, breakRoot, continueRoot, ?_⟩⟩
  · omega
  · intro n b hn
    generalize he : child p n b = e
    cases e with
    | node m =>
        have h := rankEdge n b m hn he
        change rank m + 1 < rank n + 1
        omega
    | inc r => change 0 < rank n + 1; omega
    | decnz r => change 0 < rank n + 1; omega
    | brk k => change 0 < rank n + 1; omega
    | cont k => change 0 < rank n + 1; omega
    | halt => change 0 < rank n + 1; omega
  · intro n hn
    have hbl : bE B (p.nodes n).1 - 1 ≤ B n := by
      rw [breakEq n hn]
      exact Nat.le_max_left _ _
    have hbr : bE B (p.nodes n).2 ≤ B n := by
      rw [breakEq n hn]
      exact Nat.le_max_right _ _
    have hcl : cE C (p.nodes n).1 ≤ C n := by
      rw [continueEq n hn]
      exact Nat.le_max_left _ _
    have hcr : cE C (p.nodes n).2 - 1 ≤ C n := by
      rw [continueEq n hn]
      exact Nat.le_max_right _ _
    exact ⟨by omega, hbr, hcl, by omega⟩

end SetTheory.BusyBeaver.ZFC.RMEquiv
