import DiophantineConsistency.ArithmeticDAGDegree
import DiophantineConsistency.ArithmeticDAGPowers

/-!
# Proposed generic circuit-proof infrastructure

This file preserves the repository's list evaluator and topology definition.
Checked with Lean 4.32.0 against ProveIt commit 60e9c5d620c6.
All six audited theorems use only propext, Classical.choice, and Quot.sound
(or a subset); the separate validation log records the exact dependencies.
No literal circuit, input transformation, or degree bound is replaced by a
hypothesis here: each theorem states the local obligations it requires.
-/
namespace DiophantineConsistency.Refactoring
open ArithmeticDAG

variable {inputs fixed : ℕ} {R : Type*} [CommRing R]

/-- Topological induction with the evaluator equation supplied once. -/
theorem run_invariant (p : Fin fixed → R) (x : Fin inputs → R)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes)
    (P : ℕ → R → Prop)
    (step : ∀ i, i < nodes.length →
      (∀ j ∈ (nodes.getD i (.literal 0)).dependencies,
        P j ((run p x nodes []).getD j 0)) →
      P i ((nodes.getD i (.literal 0)).evalAt p x
        (fun j => (run p x nodes []).getD j 0))) :
    ∀ i, i < nodes.length → P i ((run p x nodes []).getD i 0) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    rw [run_node_equation p x nodes htop i hi]
    apply step i hi
    intro j hj
    exact ih j (htop ⟨i, hi⟩ j hj) ((htop ⟨i, hi⟩ j hj).trans hi)

/-- Same statement as run_eq_of_node_equations, using the generic invariant. -/
theorem run_eq_of_node_equations_short (p : Fin fixed → R) (x : Fin inputs → R)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes) (v : ℕ → R)
    (hv : ∀ i < nodes.length, v i = (nodes.getD i (.literal 0)).evalAt p x v) :
    ∀ i < nodes.length, (run p x nodes []).getD i 0 = v i := by
  apply run_invariant p x nodes htop (fun i z => z = v i)
  intro i hi hprev
  rw [hv i hi]
  exact Node.evalAt_congr p x _ v _ hprev

/-- Same degree guarantee; only the shared induction is factored out. -/
theorem value_degree_le_short {σ : Type*} (p : Fin fixed → ℤ)
    (v : Fin inputs → MvPolynomial σ ℤ) (inputDegree : Fin inputs → ℕ)
    (hv : ∀ k, (v k).totalDegree ≤ inputDegree k)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes)
    (label : ℕ → ℕ) (hcert : DegreeCertificate nodes inputDegree label)
    (output : ℕ) (ho : output < nodes.length) :
    (value nodes output (fun k => MvPolynomial.C (p k)) v).totalDegree ≤ label output :=
  run_invariant (fun k => MvPolynomial.C (p k)) v nodes htop
    (fun i q => q.totalDegree ≤ label i)
    (fun i hi hprev =>
      Node.evalAt_degree_le p v inputDegree hv _ label i _ (hcert ⟨i, hi⟩) hprev)
    output ho

/-- The same input-irrelevance lemma is private in both translation modules. -/
theorem evalAt_input_irrelevant (p : Fin fixed → R) (x y : Fin inputs → R)
    (v : ℕ → R) (n : Node inputs fixed) (h : ∀ j, n ≠ .input j) :
    n.evalAt p x v = n.evalAt p y v := by
  cases n <;> simp only [Node.evalAt]
  exact False.elim (h _ rfl)

/-- Commutative gates allow swapped operands; subtraction remains ordered. -/
def NodeRelComm (rel : ℕ → ℕ → Prop) : Node inputs fixed → Node inputs fixed → Prop
  | .literal a, .literal b => a = b
  | .input a, .input b => a = b
  | .constant a, .constant b => a = b
  | .add a b, .add c d | .mul a b, .mul c d =>
      (rel a c ∧ rel b d) ∨ (rel a d ∧ rel b c)
  | .sub a b, .sub c d => rel a c ∧ rel b d
  | _, _ => False

instance (rel : ℕ → ℕ → Prop) [DecidableRel rel] (n m : Node inputs fixed) :
    Decidable (NodeRelComm rel n m) := by
  cases n <;> cases m <;> simp only [NodeRelComm] <;> infer_instance

/-- Soundness is an ordinary kernel-checked ring theorem. -/
theorem evalAt_of_NodeRelComm (p : Fin fixed → R) (x : Fin inputs → R)
    (rel : ℕ → ℕ → Prop) (old new : Node inputs fixed) (v w : ℕ → R)
    (h : NodeRelComm rel old new) (hv : ∀ i j, rel i j → w j = v i) :
    new.evalAt p x w = old.evalAt p x v := by
  cases old <;> cases new <;> simp_all only [NodeRelComm, Node.evalAt]
  all_goals
    first
    | exact congrArg₂ (fun a b : R => a - b) (hv _ _ h.1) (hv _ _ h.2)
    | (rcases h with h | h
       · rw [hv _ _ h.1, hv _ _ h.2]
       · rw [hv _ _ h.2, hv _ _ h.1]
         first | exact add_comm _ _ | exact mul_comm _ _)

/-- Finite-table adapter for the existing run_power theorem. -/
theorem register_power_of_certificate (p : Fin fixed → R) (x : Fin inputs → R)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes)
    (label : ℕ → ℕ) (base : ℕ) (hbase : label base = 1)
    (cert : ∀ j : Fin nodes.length, j.val ≠ base → label j.val ≠ 0 →
      PowerStep nodes label j.val)
    (i : Fin nodes.length) (hi : label i.val ≠ 0) :
    (run p x nodes []).getD i.val 0 =
      ((run p x nodes []).getD base 0) ^ label i.val :=
  run_power p x nodes htop label base hbase
    (fun j hj => cert ⟨j, hj⟩) i.val i.isLt hi

end DiophantineConsistency.Refactoring

#print axioms DiophantineConsistency.Refactoring.run_invariant
#print axioms DiophantineConsistency.Refactoring.run_eq_of_node_equations_short
#print axioms DiophantineConsistency.Refactoring.value_degree_le_short
#print axioms DiophantineConsistency.Refactoring.evalAt_input_irrelevant
#print axioms DiophantineConsistency.Refactoring.evalAt_of_NodeRelComm

#print axioms DiophantineConsistency.Refactoring.register_power_of_certificate
