import DiophantineConsistency.ArithmeticDAGDegree
import DiophantineConsistency.NaturalDAGQuartic

/-!
Proposed shared facts, plus same-statement replacements for existing proofs.
No source DAG, representation, witness count, or topology condition changes.
Verification status is recorded separately by the reproduction driver.
-/

namespace DiophantineConsistency.ProofRefactoring

open ArithmeticDAG

variable {inputs fixed : ℕ} {R : Type*} [CommRing R]

/-- A local invariant propagates through a topological arithmetic DAG. -/
theorem run_invariant (p : Fin fixed → R) (x : Fin inputs → R)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes)
    (P : ℕ → R → Prop)
    (hlocal : ∀ i < nodes.length, ∀ v : ℕ → R,
      (∀ j ∈ (nodes.getD i (.literal 0)).dependencies, P j (v j)) →
      P i ((nodes.getD i (.literal 0)).evalAt p x v)) :
    ∀ i < nodes.length, P i ((run p x nodes []).getD i 0) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    rw [run_node_equation p x nodes htop i hi]
    apply hlocal i hi
    intro j hj
    have hji := htop ⟨i, hi⟩ j hj
    exact ih j hji (hji.trans hi)

/-- Same conclusion as NaturalDAGQuartic.run_nonnegative. -/
theorem run_nonnegative_short (nodes : List (Node inputs fixed))
    (htop : Topological nodes) (p : Fin fixed → ℤ)
    (ha : NaturalDAGQuartic.Allowed nodes p) (x : Fin inputs → ℕ) :
    ∀ j < nodes.length, 0 ≤ (run p (fun i => (x i : ℤ)) nodes []).getD j 0 :=
  run_invariant p (fun i => (x i : ℤ)) nodes htop (fun _ z => 0 ≤ z)
    (fun j hj v hv =>
      NaturalDAGQuartic.node_nonnegative p x v _ (ha ⟨j, hj⟩) hv)

/-- Same conclusion as ArithmeticDAG.value_degree_le. -/
theorem value_degree_le_short {σ : Type*} (p : Fin fixed → ℤ)
    (v : Fin inputs → MvPolynomial σ ℤ) (inputDegree : Fin inputs → ℕ)
    (hv : ∀ k, (v k).totalDegree ≤ inputDegree k)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes)
    (label : ℕ → ℕ) (hcert : DegreeCertificate nodes inputDegree label)
    (output : ℕ) (ho : output < nodes.length) :
    (value nodes output (fun k => MvPolynomial.C (p k)) v).totalDegree ≤
      label output :=
  run_invariant (fun k => MvPolynomial.C (p k)) v nodes htop
    (fun i q => q.totalDegree ≤ label i)
    (fun i hi values hprev =>
      Node.evalAt_degree_le p v inputDegree hv values label i _ (hcert ⟨i, hi⟩) hprev)
    output ho

/-- Same conclusion as ArithmeticDAG.run_eq_of_node_equations. -/
theorem run_eq_of_node_equations_short (p : Fin fixed → R) (x : Fin inputs → R)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes) (v : ℕ → R)
    (hv : ∀ i < nodes.length,
      v i = (nodes.getD i (.literal 0)).evalAt p x v) :
    ∀ i < nodes.length, (run p x nodes []).getD i 0 = v i :=
  run_invariant p x nodes htop (fun i z => z = v i)
    (fun i hi values hprev => by
      rw [hv i hi]
      exact Node.evalAt_congr p x values v _ hprev)

/-- Publish once: this exact induction currently occurs privately in three files. -/
theorem eval_sumExpressions {σ : Type*} (es : List (Expr σ)) (v : σ → ℤ) :
    (QuarticSyntax.sumExpressions es).eval v =
      (es.map (fun e => e.eval v)).sum := by
  induction es <;> simp_all [QuarticSyntax.sumExpressions]

/-- Shared front end for the three executable sum-of-squares compilers. -/
theorem sumSquares_zero_iff {σ : Type*} {n : ℕ}
    (residual : Fin n → Expr σ) (v : σ → ℤ) :
    (QuarticSyntax.sumExpressions
      (List.ofFn fun i => residual i * residual i)).eval v = 0 ↔
      ∀ i, (residual i).eval v = 0 := by
  rw [eval_sumExpressions]
  simp only [List.map_ofFn, Fin.sum_ofFn, Function.comp_apply, Expr.eval_mul]
  simpa only [Finset.mem_univ, forall_true_left] using
    (Finset.sum_mul_self_eq_zero_iff (Finset.univ : Finset (Fin n))
      (fun i => (residual i).eval v))

/-- Parameterized form of QuarticCost.sumExpressions_binaryOps_le. -/
theorem sumExpressions_binaryOps_bound {σ : Type*} (es : List (Expr σ)) (b : ℕ)
    (h : ∀ e ∈ es, e.binaryOps ≤ b) :
    (QuarticSyntax.sumExpressions es).binaryOps ≤ (b + 1) * es.length := by
  induction es with
  | nil => simp [QuarticSyntax.sumExpressions, Expr.binaryOps]
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun e he => h e (by simp [he]))
    change 1 + e.binaryOps + (QuarticSyntax.sumExpressions es).binaryOps ≤ _
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

#print axioms run_invariant
#print axioms run_nonnegative_short
#print axioms value_degree_le_short
#print axioms run_eq_of_node_equations_short
#print axioms sumSquares_zero_iff
#print axioms sumExpressions_binaryOps_bound

end DiophantineConsistency.ProofRefactoring
