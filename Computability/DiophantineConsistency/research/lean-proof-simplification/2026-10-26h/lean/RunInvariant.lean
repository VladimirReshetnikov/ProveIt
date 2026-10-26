import DiophantineConsistency.ArithmeticDAGDegree
import DiophantineConsistency.NaturalDAGQuartic

/-! One induction rule for local invariants of topological DAGs. -/

namespace DiophantineConsistency.ProofRefactor

open ArithmeticDAG

theorem run_invariant {inputs fixed : ℕ} {R : Type*} [CommRing R]
    (p : Fin fixed → R) (x : Fin inputs → R)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes)
    (P : ℕ → R → Prop)
    (hstep : ∀ i < nodes.length, ∀ v : ℕ → R,
      (∀ j ∈ (nodes.getD i (.literal 0)).dependencies, P j (v j)) →
      P i ((nodes.getD i (.literal 0)).evalAt p x v)) :
    ∀ i < nodes.length, P i ((run p x nodes []).getD i 0) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    rw [run_node_equation p x nodes htop i hi]
    apply hstep i hi
    intro j hj
    have hji := htop ⟨i, hi⟩ j hj
    exact ih j hji (hji.trans hi)

theorem run_nonnegative {inputs fixed : ℕ} (nodes : List (Node inputs fixed))
    (htop : Topological nodes) (p : Fin fixed → ℤ)
    (ha : NaturalDAGQuartic.Allowed nodes p) (x : Fin inputs → ℕ) :
    ∀ j < nodes.length, 0 ≤ (run p (fun i => (x i : ℤ)) nodes []).getD j 0 := by
  apply run_invariant p (fun i => (x i : ℤ)) nodes htop (fun _ z => 0 ≤ z)
  intro i hi v hv
  exact NaturalDAGQuartic.node_nonnegative p x v _ (ha ⟨i, hi⟩) hv

theorem value_degree_le {inputs fixed : ℕ} {σ : Type*} (p : Fin fixed → ℤ)
    (v : Fin inputs → MvPolynomial σ ℤ) (inputDegree : Fin inputs → ℕ)
    (hv : ∀ k, (v k).totalDegree ≤ inputDegree k)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes)
    (label : ℕ → ℕ) (hcert : DegreeCertificate nodes inputDegree label)
    (output : ℕ) (ho : output < nodes.length) :
    (value nodes output (fun k => MvPolynomial.C (p k)) v).totalDegree ≤ label output := by
  exact run_invariant (fun k => MvPolynomial.C (p k)) v nodes htop
    (fun i q => q.totalDegree ≤ label i)
    (fun i hi values hprev =>
      Node.evalAt_degree_le p v inputDegree hv values label i _ (hcert ⟨i, hi⟩) hprev)
    output ho

#print axioms run_invariant
#print axioms NaturalDAGQuartic.run_nonnegative
#print axioms run_nonnegative
#print axioms ArithmeticDAG.value_degree_le
#print axioms value_degree_le

end DiophantineConsistency.ProofRefactor
