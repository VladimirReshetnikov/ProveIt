import DiophantineConsistency.ArithmeticDAGPowers

/-! A proposed relation for circuit-translation certificates. Subtraction
remains ordered; only addition and multiplication allow operand exchange. -/
namespace DiophantineConsistency.RefactoringReview
open ArithmeticDAG

variable {inputs fixed : ℕ}

def NodeRelComm (rel : ℕ → ℕ → Prop) : Node inputs fixed → Node inputs fixed → Prop
  | .add a b, .add c d | .mul a b, .mul c d =>
      (rel a c ∧ rel b d) ∨ (rel a d ∧ rel b c)
  | n, m => NodeRel rel n m

instance (rel : ℕ → ℕ → Prop) [DecidableRel rel] (n m : Node inputs fixed) :
    Decidable (NodeRelComm rel n m) := by
  cases n <;> cases m <;> simp only [NodeRelComm, NodeRel] <;> infer_instance

theorem evalAt_of_NodeRelComm {R : Type*} [CommRing R]
    (p : Fin fixed → R) (x : Fin inputs → R)
    (rel : ℕ → ℕ → Prop) (old new : Node inputs fixed) (v w : ℕ → R)
    (h : NodeRelComm rel old new) (hv : ∀ i j, rel i j → w j = v i) :
    new.evalAt p x w = old.evalAt p x v := by
  cases old <;> cases new <;> simp_all [NodeRelComm, NodeRel, Node.evalAt]
  all_goals first
    | (rcases h with h | h
       · rw [hv _ _ h.1, hv _ _ h.2]
       · rw [hv _ _ h.2, hv _ _ h.1]
         first | exact add_comm _ _ | exact mul_comm _ _)
    | rw [hv _ _ h.1, hv _ _ h.2]

#print axioms evalAt_of_NodeRelComm

end DiophantineConsistency.RefactoringReview
