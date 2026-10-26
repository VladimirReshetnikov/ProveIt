import BoundedZFCConsistency.OmegaRecursion
import BoundedZFCConsistency.CodePredicate

/-! Early zero/successor decomposition for arbitrary internal naturals.
The following block is moved unchanged from InternalSat. -/
namespace LeanProofs.BoundedZFCConsistency
open SetTheory SetTheory.Form
universe u
variable {V : Type u} {mem : V → V → Prop}

/-! ## Case analysis on internal natural numbers

The internal arithmetic of `ZF.Zf`, extended by
`BoundedZFCConsistency.OmegaRecursion`, has transitivity, irreflexivity,
injectivity of the successor, and linearity, but not the fact that the
successor is onto the nonzero naturals.  That fact is what makes the shifted
environment *total*, so it is proved here, by the definable-induction
schema. -/

/-- "slot `0` is zero or a successor of an internal natural".

| de Bruijn slot | contents                   |
| -------------- | -------------------------- |
| `0`            | the predecessor `m`        |
| `1`            | the induction variable `n` |
| `k+1`          | the caller's slot `k`      |
-/
def fZeroOrSuccF : Form :=
  fOr (fEmptyF 0) (fEx (fAnd (fNatF 0) (fSuccF 1 0)))

theorem fZeroOrSuccF_spec (H : ZFAxioms mem) (n : V) (e : Nat → V) :
    Sat mem (scons n e) fZeroOrSuccF ↔
      (n = vempty H ∨ ∃ m, mem m (omegaV H) ∧ n = vsucc H m) := by
  exact or_congr (fEmptyF_spec H (scons n e) 0)
    (exists_congr fun m => and_congr
      (fNatF_spec H (scons m (scons n e)) 0)
      (fSuccF_spec H (scons m (scons n e)) 1 0))

/-- **Every internal natural is zero or a successor.**  The induction is
immediate; what it buys is a case analysis that external recursion cannot
supply, because a nonstandard natural is not reachable from zero by finitely
many external steps. -/
theorem nat_zero_or_succ (H : ZFAxioms mem) :
    ∀ n, mem n (omegaV H) →
      (n = vempty H ∨ ∃ m, mem m (omegaV H) ∧ n = vsucc H m) := by
  intro n hn
  refine (fZeroOrSuccF_spec H n (fun _ => vempty H)).mp ?_
  refine omega_ind H fZeroOrSuccF (fun _ => vempty H) ?_ ?_ n hn
  · exact (fZeroOrSuccF_spec H (vempty H) (fun _ => vempty H)).mpr (Or.inl rfl)
  · intro k hk _
    exact (fZeroOrSuccF_spec H (vsucc H k) (fun _ => vempty H)).mpr
      (Or.inr ⟨k, hk, rfl⟩)

end LeanProofs.BoundedZFCConsistency
