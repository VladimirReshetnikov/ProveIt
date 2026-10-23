import DiophantineConsistency.ArithmeticDAGSemantics
import Mathlib.Algebra.MvPolynomial.Degrees

/-! # Kernel-checked degree bounds for shared arithmetic circuits

Degree labels certify upper bounds. Addition and subtraction may cancel
leading terms, so labels alone do not establish exact degrees.
-/

namespace DiophantineConsistency.ArithmeticDAG

variable {inputs fixed : ℕ}

def Node.DegreeStep (inputDegree : Fin inputs → ℕ) (label : ℕ → ℕ) (i : ℕ) :
    Node inputs fixed → Prop
  | .literal _ | .constant _ => True
  | .input k => inputDegree k ≤ label i
  | .add a b | .sub a b => max (label a) (label b) ≤ label i
  | .mul a b => label a+label b ≤ label i

def DegreeCertificate (nodes : List (Node inputs fixed)) (inputDegree : Fin inputs → ℕ)
    (label : ℕ → ℕ) : Prop :=
  ∀ i : Fin nodes.length, (nodes.getD i.val (.literal 0)).DegreeStep inputDegree label i.val

instance (n : Node inputs fixed) (d : Fin inputs → ℕ) (label : ℕ → ℕ) (i : ℕ) :
    Decidable (n.DegreeStep d label i) := by
  cases n <;> unfold Node.DegreeStep <;> infer_instance

instance (nodes : List (Node inputs fixed)) (d : Fin inputs → ℕ) (label : ℕ → ℕ) :
    Decidable (DegreeCertificate nodes d label) :=
  inferInstanceAs (Decidable (∀ i : Fin nodes.length,
    (nodes.getD i.val (.literal 0)).DegreeStep d label i.val))

theorem Node.evalAt_degree_le {σ : Type*} (p : Fin fixed → ℤ)
    (v : Fin inputs → MvPolynomial σ ℤ) (inputDegree : Fin inputs → ℕ)
    (hv : ∀ k, (v k).totalDegree ≤ inputDegree k) (values : ℕ → MvPolynomial σ ℤ)
    (label : ℕ → ℕ) (i : ℕ) (n : Node inputs fixed)
    (hstep : n.DegreeStep inputDegree label i)
    (hprev : ∀ j ∈ n.dependencies, (values j).totalDegree ≤ label j) :
    (n.evalAt (fun k => MvPolynomial.C (p k)) v values).totalDegree ≤ label i := by
  cases n with
  | literal z =>
    change (MvPolynomial.C z : MvPolynomial σ ℤ).totalDegree ≤ label i
    rw [MvPolynomial.totalDegree_C]
    omega
  | constant k =>
    change (MvPolynomial.C (p k) : MvPolynomial σ ℤ).totalDegree ≤ label i
    rw [MvPolynomial.totalDegree_C]
    omega
  | input k => exact (hv k).trans hstep
  | add a b =>
    exact (MvPolynomial.totalDegree_add _ _).trans
      ((max_le_max (hprev a (by simp [dependencies]))
        (hprev b (by simp [dependencies]))).trans hstep)
  | sub a b =>
    exact (MvPolynomial.totalDegree_sub _ _).trans
      ((max_le_max (hprev a (by simp [dependencies]))
        (hprev b (by simp [dependencies]))).trans hstep)
  | mul a b =>
    exact (MvPolynomial.totalDegree_mul _ _).trans
      ((Nat.add_le_add (hprev a (by simp [dependencies]))
        (hprev b (by simp [dependencies]))).trans hstep)

/-- All degree claims use the actual evaluator and its strict topology. -/
theorem value_degree_le {σ : Type*} (p : Fin fixed → ℤ)
    (v : Fin inputs → MvPolynomial σ ℤ) (inputDegree : Fin inputs → ℕ)
    (hv : ∀ k, (v k).totalDegree ≤ inputDegree k)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes)
    (label : ℕ → ℕ) (hcert : DegreeCertificate nodes inputDegree label)
    (output : ℕ) (ho : output < nodes.length) :
    (value nodes output (fun k => MvPolynomial.C (p k)) v).totalDegree ≤ label output := by
  have h : ∀ i < nodes.length,
      ((run (fun k => MvPolynomial.C (p k)) v nodes []).getD i 0).totalDegree ≤ label i := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      rw [run_node_equation (fun k => MvPolynomial.C (p k)) v nodes htop i hi]
      apply Node.evalAt_degree_le p v inputDegree hv _ label i _ (hcert ⟨i,hi⟩)
      intro j hj
      exact ih j (htop ⟨i,hi⟩ j hj) ((htop ⟨i,hi⟩ j hj).trans hi)
  exact h output ho

theorem polynomial_degree_le (p : Fin fixed → ℤ)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes)
    (label : ℕ → ℕ) (hcert : DegreeCertificate nodes (fun _ => 1) label)
    (output : ℕ) (ho : output < nodes.length) :
    (polynomial nodes output p).totalDegree ≤ label output :=
  value_degree_le p MvPolynomial.X (fun _ => 1) (fun _ => by simp)
    nodes htop label hcert output ho

end DiophantineConsistency.ArithmeticDAG
