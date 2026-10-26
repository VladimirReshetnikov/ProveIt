import DiophantineConsistency.ArithmeticDAGDegree
import DiophantineConsistency.NaturalDAGQuartic

/-!
Standalone refactoring prototypes for ProveIt commit
60e9c5d620c6c387d932876cfa2d9376f64ea56c.
These use a separate namespace and do not replace upstream declarations.
See validation.json for compilation status.
-/
namespace DiophantineConsistency.RefactoringReview
open ArithmeticDAG

variable {inputs fixed : ℕ} {R : Type*} [CommRing R]

/-- One topological induction for properties preserved by each local node. -/
theorem run_invariant (p : Fin fixed → R) (x : Fin inputs → R)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes)
    (P : ℕ → R → Prop)
    (hstep : ∀ i < nodes.length, ∀ values : ℕ → R,
      (∀ j ∈ (nodes.getD i (.literal 0)).dependencies, P j (values j)) →
      P i ((nodes.getD i (.literal 0)).evalAt p x values)) :
    ∀ i < nodes.length, P i ((run p x nodes []).getD i 0) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    rw [run_node_equation p x nodes htop i hi]
    apply hstep i hi
    intro j hj
    exact ih j (htop ⟨i, hi⟩ j hj) ((htop ⟨i, hi⟩ j hj).trans hi)

/-- Same statement as the upstream node-equation uniqueness theorem. -/
theorem run_eq_of_node_equations (p : Fin fixed → R) (x : Fin inputs → R)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes) (v : ℕ → R)
    (hv : ∀ i < nodes.length, v i = (nodes.getD i (.literal 0)).evalAt p x v) :
    ∀ i < nodes.length, (run p x nodes []).getD i 0 = v i := by
  apply run_invariant p x nodes htop (fun i z => z = v i)
  intro i hi values hprev
  exact (Node.evalAt_congr p x values v _ hprev).trans (hv i hi).symm

/-- Same statement as the upstream nonnegative-evaluation theorem. -/
theorem run_nonnegative (nodes : List (Node inputs fixed)) (htop : Topological nodes)
    (p : Fin fixed → ℤ) (ha : NaturalDAGQuartic.Allowed nodes p) (x : Fin inputs → ℕ) :
    ∀ j < nodes.length, 0 ≤ (run p (fun i => (x i : ℤ)) nodes []).getD j 0 := by
  apply run_invariant p (fun i => (x i : ℤ)) nodes htop (fun _ z => 0 ≤ z)
  intro i hi values hprev
  exact NaturalDAGQuartic.node_nonnegative p x values _ (ha ⟨i, hi⟩) hprev

/-- Same statement as the upstream upper bound for circuit degree. -/
theorem value_degree_le {σ : Type*} (p : Fin fixed → ℤ)
    (v : Fin inputs → MvPolynomial σ ℤ) (inputDegree : Fin inputs → ℕ)
    (hv : ∀ k, (v k).totalDegree ≤ inputDegree k)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes)
    (label : ℕ → ℕ) (hcert : DegreeCertificate nodes inputDegree label)
    (output : ℕ) (ho : output < nodes.length) :
    (value nodes output (fun k => MvPolynomial.C (p k)) v).totalDegree ≤ label output := by
  apply run_invariant (fun k => MvPolynomial.C (p k)) v nodes htop
    (fun i q => q.totalDegree ≤ label i) _ output ho
  intro i hi values hprev
  exact Node.evalAt_degree_le p v inputDegree hv values label i _ (hcert ⟨i, hi⟩) hprev

/-- Shared version of three identical private evaluation lemmas. -/
theorem eval_sumExpressions {σ : Type*} (es : List (Expr σ)) (v : σ → ℤ) :
    (QuarticSyntax.sumExpressions es).eval v = (es.map (fun e => e.eval v)).sum := by
  induction es <;> simp_all [QuarticSyntax.sumExpressions]

/-- The SOS zero criterion is independent of the residual compiler. -/
theorem sumSquares_zero_iff {σ : Type*} {n : ℕ}
    (residuals : Fin n → Expr σ) (v : σ → ℤ) :
    (QuarticSyntax.sumExpressions (List.ofFn fun i =>
      residuals i * residuals i)).eval v = 0 ↔
      ∀ i, (residuals i).eval v = 0 := by
  rw [eval_sumExpressions]
  simp only [List.map_ofFn, Fin.sum_ofFn, Function.comp_apply, Expr.eval_mul]
  simpa only [Finset.mem_univ, forall_true_left] using
    (Finset.sum_mul_self_eq_zero_iff (Finset.univ : Finset (Fin n))
      (fun i => (residuals i).eval v))

/-- A one-line replacement body for the signed-DAG SOS theorem. -/
theorem dag_expression_zero_iff (nodes : List (Node inputs fixed)) (output : ℕ)
    (p : Fin fixed → ℤ) (v : DAGQuartic.Variables inputs nodes.length → ℤ) :
    (DAGQuartic.expression nodes output p).eval v = 0 ↔
      ∀ i, (DAGQuartic.residual nodes output p i).eval v = 0 :=
  sumSquares_zero_iff (DAGQuartic.residual nodes output p) v

/-- A one-line replacement body for the natural-DAG SOS theorem. -/
theorem natural_expression_zero_iff (nodes : List (Node inputs fixed)) (left right : ℕ)
    (p : Fin fixed → ℤ) (v : NaturalDAGQuartic.Variables inputs nodes.length → ℤ) :
    (NaturalDAGQuartic.expression nodes left right p).eval v = 0 ↔
      ∀ i, (NaturalDAGQuartic.residual nodes left right p i).eval v = 0 :=
  sumSquares_zero_iff (NaturalDAGQuartic.residual nodes left right p) v

#print axioms run_eq_of_node_equations
#print axioms run_nonnegative
#print axioms value_degree_le
#print axioms dag_expression_zero_iff
#print axioms natural_expression_zero_iff

end DiophantineConsistency.RefactoringReview
