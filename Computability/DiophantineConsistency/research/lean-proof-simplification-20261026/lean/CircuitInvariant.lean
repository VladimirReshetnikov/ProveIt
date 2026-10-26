import DiophantineConsistency.ArithmeticDAGDegree

/-!
Standalone refactoring prototypes for ProveIt commit
60e9c5d620c6c387d932876cfa2d9376f64ea56c.
These use a separate namespace and do not replace upstream declarations.
See validation.json for compilation status.
-/
namespace DiophantineConsistency.CircuitInvariantReview
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

#print axioms run_invariant
#print axioms run_eq_of_node_equations
#print axioms value_degree_le

end DiophantineConsistency.CircuitInvariantReview
