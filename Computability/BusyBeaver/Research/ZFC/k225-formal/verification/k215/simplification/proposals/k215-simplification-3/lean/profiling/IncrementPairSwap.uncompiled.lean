import BusyBeaver.ZFC.RMTransfer

/-!
UNCOMPILED RESEARCH DRAFT. No Lean executable was available for this audit.
Interfaces checked against e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad.

This is only the generic local contract. It does not claim the actual
dagPerm overlays, finite Closed obligations, or a CFG-correctness theorem.
It introduces no axiom or sorry, but requires compiler checking before use.
-/

namespace SetTheory.BusyBeaver.ZFC.IncrementPairSwapDraft

open RMDag

def pairEffect (R : Regs) (a b : Nat) : Regs :=
  upd (upd R a (R a + 1)) b (R b + 1)

theorem pair_run {p : Prog} {n a b : Nat}
    (hn : p.nodes n = (.inc a, .inc b)) (hab : a ≠ b) (R : Regs) :
    Run p (.node n) R .normal (pairEffect R a b) := by
  have hb : upd R a (R a + 1) b = R b :=
    upd_other R (R a + 1) (Ne.symm hab)
  simpa only [pairEffect, hb] using
    (RMDag.seq hn (Run.inc a R) (Run.inc b (upd R a (R a + 1))))

theorem pairEffect_comm (R : Regs) {a b : Nat} (hab : a ≠ b) :
    pairEffect R a b = pairEffect R b a :=
  upd_comm R hab (R a + 1) (R b + 1)

/-- Arbitrary runs of the original node transfer to the swapped node. -/
theorem swap_contract {p q : Prog} {n a b : Nat}
    (hp : p.nodes n = (.inc a, .inc b))
    (hq : q.nodes n = (.inc b, .inc a)) (hab : a ≠ b) :
    ∀ R x R', Run p (.node n) R x R' → Run q (.node n) R x R' := by
  apply RMTransfer.contract (fun _ => .normal) (fun R => pairEffect R a b)
  · exact pair_run hp hab
  · intro R
    rw [pairEffect_comm R hab]
    exact pair_run hq (Ne.symm hab) R

/-
Proposed application (not implemented in this draft):

  p0 := dagPerm
  p1 := p0 with node 188 changed from (inc 6, inc 7) to (inc 7, inc 6)
  p2 := p1 with node 190 changed from (inc 6, inc 1) to (inc 1, inc 6)

Keep root 0 and use ok n := decide (n < 487). For each adjacent pair:
1. Prove finite node agreement/inside checks away from its one changed node.
2. Apply RMTransfer.closed_of_contract using swap_contract at that node.
3. Apply RMTransfer.iter_transfer; reverse by swapping p/q and a/b.

This reuses existing structural induction rather than adding a bespoke
two-exception transfer theorem. Machine-specific finite facts must still be
checked in Lean; the external CFG comparison is only supporting evidence.
-/

end SetTheory.BusyBeaver.ZFC.IncrementPairSwapDraft
