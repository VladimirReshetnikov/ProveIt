import DiophantineConsistency.ArithmeticDAG

/-! # Local node equations characterize a topological circuit's evaluation -/
namespace DiophantineConsistency.ArithmeticDAG

variable {inputs fixed : ℕ} {R : Type*} [CommRing R]

namespace Node

def evalAt (p : Fin fixed → R) (x : Fin inputs → R) (v : ℕ → R) : Node inputs fixed → R
  | .literal z => (z : R)
  | .input i => x i
  | .constant i => p i
  | .add a b => v a+v b
  | .sub a b => v a-v b
  | .mul a b => v a*v b

theorem eval_eq_evalAt (p : Fin fixed → R) (x : Fin inputs → R) (values : List R)
    (v : ℕ → R) (n : Node inputs fixed)
    (h : ∀ j ∈ n.dependencies, values.getD j 0 = v j) :
    n.eval p x values = n.evalAt p x v := by
  cases n <;> simp_all only [dependencies,List.mem_cons,List.mem_singleton,forall_eq_or_imp,
    forall_eq,eval,evalAt]

theorem evalAt_congr (p : Fin fixed → R) (x : Fin inputs → R) (v w : ℕ → R)
    (n : Node inputs fixed) (h : ∀ j ∈ n.dependencies, v j = w j) :
    n.evalAt p x v = n.evalAt p x w := by
  cases n <;> simp_all only [dependencies,List.mem_cons,List.mem_singleton,forall_eq_or_imp,
    forall_eq,evalAt]
end Node

theorem run_length (p : Fin fixed → R) (x : Fin inputs → R)
    (nodes : List (Node inputs fixed)) (values : List R) :
    (run p x nodes values).length = nodes.length+values.length := by
  induction nodes generalizing values with
  | nil => simp [run]
  | cons n ns ih => simp only [run,ih,List.length_append,List.length_singleton,List.length_cons,List.length_nil];omega

theorem run_append (p : Fin fixed → R) (x : Fin inputs → R)
    (nodes rest : List (Node inputs fixed)) (values : List R) :
    run p x (nodes++rest) values = run p x rest (run p x nodes values) := by
  induction nodes generalizing values with
  | nil => rfl
  | cons n ns ih => simp only [List.cons_append,run,ih]

theorem run_preserves_getD (p : Fin fixed → R) (x : Fin inputs → R)
    (nodes : List (Node inputs fixed)) (values : List R) (i : ℕ) (hi : i < values.length) :
    (run p x nodes values).getD i 0 = values.getD i 0 := by
  induction nodes generalizing values with
  | nil => rfl
  | cons n ns ih =>
    rw [run,ih]
    · exact List.getD_append _ _ _ _ hi
    · simp only [List.length_append,List.length_singleton]
      omega

/-- Actual evaluator values satisfy every node equation, using only earlier nodes. -/
theorem run_node_equation (p : Fin fixed → R) (x : Fin inputs → R)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes)
    (i : ℕ) (hi : i < nodes.length) :
    (run p x nodes []).getD i 0 =
      (nodes.getD i (.literal 0)).evalAt p x (fun j => (run p x nodes []).getD j 0) := by
  let n := nodes.getD i (.literal 0)
  let values := run p x (nodes.take i) []
  let after := values ++ [n.eval p x values]
  have hlen : values.length = i := by
    simp only [values,run_length,List.length_take,List.length_nil,add_zero]
    exact Nat.min_eq_left hi.le
  have hsplit : nodes = nodes.take i ++ n :: nodes.drop (i+1) := by
    have ht : nodes.take (i+1) = nodes.take i ++ [n] := by
      simpa only [n,List.getD_eq_getElem _ _ hi] using (List.take_append_getElem hi).symm
    calc
      nodes = nodes.take (i+1) ++ nodes.drop (i+1) := (List.take_append_drop (i+1) nodes).symm
      _ = _ := by rw [ht,List.append_assoc,List.singleton_append]
  have hrun : run p x nodes [] = run p x (nodes.drop (i+1)) after := by
    conv_lhs => rw [hsplit,run_append,run]
  have hself : (run p x nodes []).getD i 0 = n.eval p x values := by
    rw [hrun,run_preserves_getD]
    · rw [List.getD_append_right values _ _ i (by omega),hlen,Nat.sub_self]
      rfl
    · simp only [after,List.length_append,List.length_singleton,hlen]
      omega
  rw [hself]
  apply Node.eval_eq_evalAt
  intro j hj
  have hjlt : j < i := htop ⟨i,hi⟩ j hj
  calc
    values.getD j 0 = after.getD j 0 :=
      (List.getD_append values [n.eval p x values] 0 j (by omega)).symm
    _ = (run p x (nodes.drop (i+1)) after).getD j 0 :=
      (run_preserves_getD p x (nodes.drop (i+1)) after j (by
        simp only [after,List.length_append,List.length_singleton,hlen]
        omega)).symm
    _ = (run p x nodes []).getD j 0 := congrArg (fun vs => vs.getD j 0) hrun.symm

/-- A proposed table of node values is certified by local arithmetic identities. -/
theorem run_eq_of_node_equations (p : Fin fixed → R) (x : Fin inputs → R)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes) (v : ℕ → R)
    (hv : ∀ i < nodes.length, v i = (nodes.getD i (.literal 0)).evalAt p x v) :
    ∀ i < nodes.length, (run p x nodes []).getD i 0 = v i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    rw [run_node_equation p x nodes htop i hi,hv i hi]
    apply Node.evalAt_congr
    intro j hj
    have hji := htop ⟨i,hi⟩ j hj
    exact ih j hji (hji.trans hi)

theorem value_eq_of_node_equations (p : Fin fixed → R) (x : Fin inputs → R)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes) (output : ℕ)
    (ho : output < nodes.length) (v : ℕ → R)
    (hv : ∀ i < nodes.length, v i = (nodes.getD i (.literal 0)).evalAt p x v) :
    value nodes output p x = v output :=
  run_eq_of_node_equations p x nodes htop v hv output ho

end DiophantineConsistency.ArithmeticDAG
