import DiophantineConsistency.ScalarPRCode
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Linarith

/-!
# Certified simplification of supplied primitive-recursive programs

Simplifying the program before the Diophantine compiler can remove complete
recursion traces. Every rule preserves evaluation at every natural input.
No rule runs a search or depends on the consistency predicate.
-/

namespace DiophantineConsistency.ScalarPRCode

/-- Number of instruction nodes in the supplied finite program tree. -/
def nodeCount : ScalarPRCode → ℕ
  | .zero | .succ | .left | .right => 1
  | .pair f g | .comp f g | .prec f g => 1 + f.nodeCount + g.nodeCount

/-- Composition rules that remove constant, projection, and identity plumbing. -/
def smartComp (f g : ScalarPRCode) : ScalarPRCode :=
  match f, g with
  | .zero, _ => .zero
  | .left, .pair a _ => a
  | .right, .pair _ b => b
  | .pair .left .right, _ => g
  | _, .pair .left .right => f
  | _, _ => .comp f g

theorem eval_smartComp (f g : ScalarPRCode) (n : ℕ) :
    (smartComp f g).eval n = f.eval (g.eval n) := by
  unfold smartComp
  split <;> simp [eval, Nat.pair_unpair]

theorem nodeCount_smartComp_le (f g : ScalarPRCode) :
    (smartComp f g).nodeCount ≤ 1 + f.nodeCount + g.nodeCount := by
  unfold smartComp
  split <;> simp_all [nodeCount] <;> omega

/-- Eliminate a redundant pair of inverse projections of the same program. -/
def smartPair (f g : ScalarPRCode) : ScalarPRCode :=
  match f, g with
  | .zero, .zero => .zero
  | .comp .left a, .comp .right b => if a = b then a else .pair f g
  | _, _ => .pair f g

theorem eval_smartPair (f g : ScalarPRCode) (n : ℕ) :
    (smartPair f g).eval n = Nat.pair (f.eval n) (g.eval n) := by
  unfold smartPair
  split
  · rfl
  · split_ifs with h
    · subst h
      simp [eval, Nat.pair_unpair]
    · rfl
  · rfl

theorem nodeCount_smartPair_le (f g : ScalarPRCode) :
    (smartPair f g).nodeCount ≤ 1 + f.nodeCount + g.nodeCount := by
  unfold smartPair
  split <;> simp_all [nodeCount]
  split_ifs <;> simp_all [nodeCount]
  omega

private theorem rec_previous (f : ℕ → ℕ) (z k : ℕ) :
    Nat.rec (f z) (fun _ acc => acc) k = f z := by
  induction k <;> simp_all

private theorem rec_counter (k : ℕ) :
    Nat.rec 0 (fun _ acc => acc + 1) k = k := by
  induction k <;> simp_all

private theorem rec_zero (k : ℕ) : Nat.rec (motive := fun _ => ℕ) 0 (fun _ _ => 0) k = 0 := by
  induction k <;> simp_all

/-- Remove constant-zero, unchanged-accumulator, and pure-counter recursions. -/
def smartPrec (f g : ScalarPRCode) : ScalarPRCode :=
  match f, g with
  | .zero, .zero => .zero
  | _, .comp .right .right => smartComp f .left
  | .zero, .comp .succ (.comp .right .right) => .right
  | _, _ => .prec f g

theorem eval_smartPrec (f g : ScalarPRCode) (n : ℕ) :
    (smartPrec f g).eval n = (ScalarPRCode.prec f g).eval n := by
  unfold smartPrec
  split
  · simpa only [eval] using (rec_zero n.unpair.2).symm
  · simp only [eval_smartComp, eval, Nat.unpair_pair]
    exact (rec_previous _ _ _).symm
  · simp only [eval, Nat.unpair_pair]
    exact (rec_counter _).symm
  · rfl

theorem nodeCount_smartPrec_le (f g : ScalarPRCode) :
    (smartPrec f g).nodeCount ≤ 1 + f.nodeCount + g.nodeCount := by
  unfold smartPrec
  split
  · simp [nodeCount]
  · exact (nodeCount_smartComp_le _ _).trans (by simp [nodeCount])
  · simp [nodeCount]
  · rfl

/-- Simplify every subprogram, preserving executable program data. -/
def optimize : ScalarPRCode → ScalarPRCode
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .pair f g => smartPair f.optimize g.optimize
  | .comp f g => smartComp f.optimize g.optimize
  | .prec f g => smartPrec f.optimize g.optimize

theorem eval_optimize (c : ScalarPRCode) (n : ℕ) : c.optimize.eval n = c.eval n := by
  induction c generalizing n with
  | zero | succ | left | right => rfl
  | pair f g hf hg => simp only [optimize, eval_smartPair, eval, hf, hg]
  | comp f g hf hg => simp only [optimize, eval_smartComp, eval, hf, hg]
  | prec f g hf hg =>
      simp only [optimize, eval_smartPrec, eval, hf, hg]

/-- The optimizer never increases the finite program tree. -/
theorem nodeCount_optimize_le (c : ScalarPRCode) : c.optimize.nodeCount ≤ c.nodeCount := by
  induction c with
  | zero | succ | left | right => rfl
  | pair f g hf hg =>
      exact (nodeCount_smartPair_le _ _).trans (by simp only [nodeCount]; omega)
  | comp f g hf hg =>
      exact (nodeCount_smartComp_le _ _).trans (by simp only [nodeCount]; omega)
  | prec f g hf hg =>
      exact (nodeCount_smartPrec_le _ _).trans (by simp only [nodeCount]; omega)

namespace Realizes

/-- Simplify a supplied program while retaining its original specification. -/
def optimize {f : ℕ → ℕ} (p : Realizes f) : Realizes f :=
  ⟨p.val.optimize, fun n => (eval_optimize p.val n).trans (p.property n)⟩

end Realizes
end DiophantineConsistency.ScalarPRCode
