import DiophantineConsistency.WitnessCompaction
import DiophantineConsistency.SimplifiedJones
import DiophantineConsistency.ExecutableJones

/-!
# Jones syntax after removing unused source witnesses

Constant and zero simplification can delete every occurrence of an original
witness. Deduplicating the remaining coordinate list removes those slots
before quartic compilation, while preserving solvability and all gate counts.
-/

namespace DiophantineConsistency.CompactedJones

open Jones1982

def retainedWitnesses {A : Prop} (r : Rep Empty (fun _ => A)) : ℕ :=
  WitnessCompaction.count (SimplifiedJones.left r) (SimplifiedJones.right r)

def left {A : Prop} (r : Rep Empty (fun _ => A)) :=
  WitnessCompaction.leftClosed (SimplifiedJones.left r) (SimplifiedJones.right r)

def right {A : Prop} (r : Rep Empty (fun _ => A)) :=
  WitnessCompaction.rightClosed (SimplifiedJones.left r) (SimplifiedJones.right r)

def witnessCount {A : Prop} (r : Rep Empty (fun _ => A)) : ℕ :=
  QuarticCompiler.witnessCount (left r) (right r)

theorem retainedWitnesses_le {A : Prop} (r : Rep Empty (fun _ => A)) :
    retainedWitnesses r ≤ r.witnessCount := WitnessCompaction.count_le _ _

theorem witnessCount_le_simplified {A : Prop} (r : Rep Empty (fun _ => A)) :
    witnessCount r ≤ SimplifiedJones.witnessCount r := by
  have h := retainedWitnesses_le r
  change retainedWitnesses r + (QuarticCompiler.Gates.count (left r) +
    (QuarticCompiler.Gates.count (right r) + 1)) ≤
    r.witnessCount + (QuarticCompiler.Gates.count (SimplifiedJones.left r) +
      (QuarticCompiler.Gates.count (SimplifiedJones.right r) + 1))
  simp only [left, right, WitnessCompaction.count_leftClosed,
    WitnessCompaction.count_rightClosed]
  omega

theorem witnessCount_le {A : Prop} (r : Rep Empty (fun _ => A)) :
    witnessCount r ≤ (QuarticCompiler.compile r).ν :=
  (witnessCount_le_simplified r).trans (SimplifiedJones.witnessCount_le r)

/-- The positional exponent parameter cannot increase after gate deletion. -/
theorem Lexp_le {A : Prop} (r : Rep Empty (fun _ => A)) :
    Lexp (witnessCount r) 4 ≤ Lexp (QuarticCompiler.compile r).ν 4 := by
  exact pow_le_pow_right₀ (by decide : 1 ≤ (5 : ℕ))
    (Nat.add_le_add_right (witnessCount_le r) 1)

theorem wset_iff {A : Prop} (r : Rep Empty (fun _ => A)) (x : ℕ) :
    Wset (QuarticCompiler.quartic (left r) (right r)) x ↔ A := by
  rw [QuarticCompiler.wset_quartic_iff]
  apply (WitnessCompaction.exists_closed_eval_eq_iff
    (SimplifiedJones.left r) (SimplifiedJones.right r)).symm.trans
  simpa only [SimplifiedJones.left, SimplifiedJones.right, NatExpr.eval_simplify] using
    (r.correct_splitNatural Empty.elim).symm

/-- Normalized quartic data with a nonincreasing number of witness slots. -/
noncomputable def compile {A : Prop} (r : Rep Empty (fun _ => A)) : QuarticCompiler.Result A :=
  { ν := witnessCount r
    positive := by dsimp only [witnessCount, QuarticCompiler.witnessCount]; omega
    polynomial := QuarticCompiler.quartic (left r) (right r)
    degree := QuarticCompiler.quartic_degree _ _
    normalized := QuarticCompiler.quartic_normalized _ _
    correct := wset_iff r }

/-- Executable final syntax using the simplified natural gate source. -/
def expression {A : Prop} (r : Rep Empty (fun _ => A)) : Expr (Fin 9) :=
  ExecutableJones.expression (QuarticSyntax.expression (left r) (right r)) 0

theorem expression_correct {A : Prop} (r : Rep Empty (fun _ => A)) :
    (∃ v : Fin 9 → ℕ, (expression r).eval (fun i => (v i : ℤ)) = 0) ↔ A := by
  exact (ExecutableJones.hasNaturalZero_quartic (left r) (right r)).trans (wset_iff r 1)

theorem eval_expression {A : Prop} (r : Rep Empty (fun _ => A)) (v : Fin 9 → ℤ) :
    (expression r).eval v =
      MvPolynomial.eval v (NinePolynomial.polynomial (compile r).polynomial 0) := by
  rw [expression, ExecutableJones.eval_expression, JonesSyntax.eval_expression,
    QuarticSyntax.polynomial_expression]
  rfl

theorem noZero_expression {A : Prop} (r : Rep Empty (fun _ => A)) :
    (¬ ∃ v : Fin 9 → ℕ, (expression r).eval (fun i => (v i : ℤ)) = 0) ↔ ¬ A :=
  not_congr (expression_correct r)

end DiophantineConsistency.CompactedJones
