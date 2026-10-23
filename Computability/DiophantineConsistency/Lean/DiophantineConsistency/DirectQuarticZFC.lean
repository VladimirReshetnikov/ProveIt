import DiophantineConsistency.NativeZFC
import DiophantineConsistency.QuarticCost
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# A closed executable consistency quartic without the Jones compression

The finite variable count is determined by the supplied arithmetic graph.
No universal-polynomial index, nine-variable reduction, or native fixed
coefficient payload is used in the equation's construction.
-/

namespace DiophantineConsistency.ClosedQuartic

open MvPolynomial Jones1982

variable {A : Prop}

/-- Exact natural variable count, including the quartic normalization guard. -/
abbrev variableCount (r : Rep Empty (fun _ => A)) : ℕ :=
  QuarticCompiler.witnessCount (CompactedJones.left r) (CompactedJones.right r)

/-- The explicit sum of squared gate residuals, fixing its unused input to one.
Only the finite residual syntax is constructed; Jones compression is absent. -/
def expression (r : Rep Empty (fun _ => A)) : Expr (Fin (variableCount r)) :=
  (QuarticSyntax.expression (CompactedJones.left r) (CompactedJones.right r)).subst
    (Fin.cons (.constant 1) Expr.var)

/-- Its ordinary integer polynomial, with the distinguished input removed. -/
noncomputable def polynomial (r : Rep Empty (fun _ => A)) :
    MvPolynomial (Fin (variableCount r)) ℤ :=
  specializeOne (QuarticCompiler.quartic (CompactedJones.left r) (CompactedJones.right r))

theorem eval_expression (r : Rep Empty (fun _ => A)) (v : Fin (variableCount r) → ℤ) :
    (expression r).eval v = MvPolynomial.eval (Fin.cons 1 v)
      (QuarticCompiler.quartic (CompactedJones.left r) (CompactedJones.right r)) := by
  rw [expression,Expr.eval_subst]
  have he : (fun i : Fin (variableCount r + 1) =>
      ((Fin.cons (Expr.constant 1) Expr.var : Fin (variableCount r + 1) → Expr (Fin (variableCount r))) i).eval v) =
      Fin.cons 1 v := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [he,← Expr.eval_toPolynomial,QuarticSyntax.polynomial_expression]

theorem eval_polynomial (r : Rep Empty (fun _ => A)) (v : Fin (variableCount r) → ℤ) :
    MvPolynomial.eval v (polynomial r) = (expression r).eval v := by
  rw [polynomial,eval_specializeOne,eval_expression]

/-- The executable syntax denotes exactly the asserted ordinary polynomial. -/
theorem polynomial_expression (r : Rep Empty (fun _ => A)) :
    (expression r).toPolynomial = polynomial r := by
  apply MvPolynomial.funext
  intro v
  exact (Expr.eval_toPolynomial _ v).trans (eval_polynomial r v).symm

theorem degree_le_four (r : Rep Empty (fun _ => A)) :
    (polynomial r).totalDegree ≤ 4 :=
  (totalDegree_specializeOne_le _).trans (QuarticCompiler.quartic_degree _ _)

/-- A transparent exact recurrence for the variable count. -/
theorem variableCount_eq (r : Rep Empty (fun _ => A)) :
    variableCount r = CompactedJones.retainedWitnesses r +
      QuarticCompiler.Gates.count (CompactedJones.left r) +
      QuarticCompiler.Gates.count (CompactedJones.right r) + 1 := by
  change CompactedJones.retainedWitnesses r + (_ + (_ + 1)) = _
  omega

/-- An explicit operation bound in terms of the two source gate counts. -/
theorem binaryOps_le (r : Rep Empty (fun _ => A)) :
    (expression r).binaryOps ≤ 6 *
      (QuarticCompiler.Gates.count (CompactedJones.left r) +
        QuarticCompiler.Gates.count (CompactedJones.right r) + 2) := by
  have hf : ∀ i : Fin (variableCount r + 1),
      ((Fin.cons (Expr.constant 1) Expr.var :
        Fin (variableCount r + 1) → Expr (Fin (variableCount r))) i).binaryOps = 0 := by
    intro i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [expression,Expr.binaryOps_subst_atoms _ _ hf]
  exact QuarticCost.expression_binaryOps_le _ _

/-- A coarser bound needs only the total number of natural variables.
The count charges syntax-tree operations; DAG sharing may reduce it. -/
theorem binaryOps_le_six_mul_variables (r : Rep Empty (fun _ => A)) :
    (expression r).binaryOps ≤ 6 * (variableCount r + 1) := by
  have hcount := variableCount_eq r
  exact (binaryOps_le r).trans (Nat.mul_le_mul_left 6 (by omega))

theorem hasSyntaxZero_iff (r : Rep Empty (fun _ => A)) :
    (∃ v : Fin (variableCount r) → ℕ,
      (expression r).eval (fun i => (v i : ℤ)) = 0) ↔ A := by
  refine Iff.trans ?_ (CompactedJones.wset_iff r 1)
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨Fin.cons 1 v,rfl,?_⟩
    rw [eval_expression] at hv
    have he : (fun i => ((Fin.cons 1 v : Fin (variableCount r + 1) → ℕ) i : ℤ)) =
        Fin.cons 1 (fun i => (v i : ℤ)) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [he]
    exact hv
  · rintro ⟨v,h0,hv⟩
    refine ⟨Fin.tail v,?_⟩
    rw [eval_expression]
    have he : Fin.cons 1 (fun i => (Fin.tail v i : ℤ)) = fun i => (v i : ℤ) := by
      funext i
      refine Fin.cases ?_ (fun _ => rfl) i
      simpa using congrArg (fun n : ℕ => (n : ℤ)) h0.symm
    rw [he]
    exact hv

theorem hasNaturalZero_iff (r : Rep Empty (fun _ => A)) :
    HasNaturalZero (polynomial r) ↔ A := by
  simpa only [HasNaturalZero,eval_polynomial] using hasSyntaxZero_iff r

theorem noNaturalZero_iff (r : Rep Empty (fun _ => A)) :
    (¬ HasNaturalZero (polynomial r)) ↔ ¬ A := not_congr (hasNaturalZero_iff r)

end DiophantineConsistency.ClosedQuartic

namespace DiophantineConsistency.DirectQuarticZFC

attribute [local irreducible] NativeZFC.representation ClosedQuartic.expression

open SetTheory LeanProofs.BoundedZFCConsistency

def variableCount : ℕ := ClosedQuartic.variableCount NativeZFC.representation

def expression : Expr (Fin variableCount) := ClosedQuartic.expression NativeZFC.representation

noncomputable def polynomial : MvPolynomial (Fin variableCount) ℤ :=
  ClosedQuartic.polynomial NativeZFC.representation

theorem eval_polynomial (v : Fin variableCount → ℤ) :
    MvPolynomial.eval v polynomial = expression.eval v :=
  ClosedQuartic.eval_polynomial NativeZFC.representation v

theorem degree_le_four : polynomial.totalDegree ≤ 4 :=
  ClosedQuartic.degree_le_four NativeZFC.representation

theorem polynomial_expression : expression.toPolynomial = polynomial :=
  ClosedQuartic.polynomial_expression NativeZFC.representation

theorem variableCount_eq : variableCount = NativeZFC.sourceWitnessCount := rfl

theorem binaryOps_le : expression.binaryOps ≤ 6 * (variableCount + 1) :=
  ClosedQuartic.binaryOps_le_six_mul_variables NativeZFC.representation

theorem hasNaturalZero_iff_refutation :
    HasNaturalZero polynomial ↔ BProv ZFCax_s [] Form.fBot :=
  ClosedQuartic.hasNaturalZero_iff NativeZFC.representation

/-- Closed external correctness, with no supplied representation, program,
compiler premise, or consistency hypothesis. -/
theorem noNaturalZero_iff_conZFC : (¬ HasNaturalZero polynomial) ↔ ConZFC :=
  ClosedQuartic.noNaturalZero_iff NativeZFC.representation

theorem noSyntaxZero_iff_conZFC :
    (¬ ∃ v : Fin variableCount → ℕ, expression.eval (fun i => (v i : ℤ)) = 0) ↔ ConZFC :=
  not_congr (ClosedQuartic.hasSyntaxZero_iff NativeZFC.representation)

end DiophantineConsistency.DirectQuarticZFC
