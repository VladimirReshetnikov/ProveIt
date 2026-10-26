import DiophantineConsistency.ArithmeticDAGDegree

namespace DiophantineConsistency.ProofRefactoring

open ArithmeticDAG
variable {inputs fixed : ℕ} {R : Type*} [CommRing R]

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

theorem run_eq_of_node_equations_short (p : Fin fixed → R) (x : Fin inputs → R)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes) (v : ℕ → R)
    (hv : ∀ i < nodes.length,
      v i = (nodes.getD i (.literal 0)).evalAt p x v) :
    ∀ i < nodes.length, (run p x nodes []).getD i 0 = v i :=
  run_invariant p x nodes htop (fun i z => z = v i)
    (fun i hi values hprev => by
      rw [hv i hi]
      exact Node.evalAt_congr p x values v _ hprev)

#print axioms run_invariant
#print axioms value_degree_le_short
#print axioms run_eq_of_node_equations_short

end DiophantineConsistency.ProofRefactoring
