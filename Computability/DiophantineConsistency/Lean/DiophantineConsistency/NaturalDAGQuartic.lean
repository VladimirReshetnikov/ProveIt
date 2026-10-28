import DiophantineConsistency.DAGQuartic

/-!
# A smaller gate quartic for circuits with nonnegative intermediate values

The circuit uses nonnegative constants, natural inputs, addition and
multiplication. Comparing two output wires supplies the final equality.
Only one natural variable per node is needed, retaining all DAG sharing.
-/

namespace DiophantineConsistency.NaturalDAGQuartic

open ArithmeticDAG
variable {inputs fixed : ℕ}

def NodeAllowed (p : Fin fixed → ℤ) : Node inputs fixed → Prop
  | .literal z => 0 ≤ z
  | .constant i => 0 ≤ p i
  | .sub _ _ => False
  | _ => True

def Allowed (nodes : List (Node inputs fixed)) (p : Fin fixed → ℤ) : Prop :=
  ∀ i : Fin nodes.length, NodeAllowed p (nodes.getD i.val (.literal 0))

instance (p : Fin fixed → ℤ) (n : Node inputs fixed) : Decidable (NodeAllowed p n) := by
  cases n <;> unfold NodeAllowed <;> infer_instance

instance (nodes : List (Node inputs fixed)) (p : Fin fixed → ℤ) : Decidable (Allowed nodes p) :=
  inferInstanceAs (Decidable (∀ i : Fin nodes.length, NodeAllowed p (nodes.getD i.val (.literal 0))))

theorem node_nonnegative (p : Fin fixed → ℤ) (x : Fin inputs → ℕ) (v : ℕ → ℤ)
    (n : Node inputs fixed) (hn : NodeAllowed p n)
    (hv : ∀ j ∈ n.dependencies, 0 ≤ v j) :
    0 ≤ n.evalAt p (fun i => (x i : ℤ)) v := by
  cases n with
  | literal z => exact hn
  | input i => exact Int.natCast_nonneg _
  | constant i => exact hn
  | add a b => exact add_nonneg (hv a (by simp [Node.dependencies])) (hv b (by simp [Node.dependencies]))
  | mul a b => exact mul_nonneg (hv a (by simp [Node.dependencies])) (hv b (by simp [Node.dependencies]))
  | sub a b => exact hn.elim

theorem run_nonnegative (nodes : List (Node inputs fixed)) (htop : Topological nodes)
    (p : Fin fixed → ℤ) (ha : Allowed nodes p) (x : Fin inputs → ℕ) :
    ∀ j < nodes.length, 0 ≤ (run p (fun i => (x i : ℤ)) nodes []).getD j 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    rw [run_node_equation p (fun i => (x i : ℤ)) nodes htop j hj]
    apply node_nonnegative p x _ _ (ha ⟨j,hj⟩)
    intro k hk
    exact ih k (htop ⟨j,hj⟩ k hk) ((htop ⟨j,hj⟩ k hk).trans hj)

abbrev Variables (inputs nodes : ℕ) := Fin inputs ⊕ Fin nodes

def wire (inputs nodes j : ℕ) : Expr (Variables inputs nodes) :=
  if h : j < nodes then .var (.inr ⟨j,h⟩) else .constant 0

def rhs (nodes : ℕ) (p : Fin fixed → ℤ) : Node inputs fixed → Expr (Variables inputs nodes)
  | .literal z => .constant z
  | .input i => .var (.inl i)
  | .constant i => .constant (p i)
  | .add a b => wire inputs nodes a + wire inputs nodes b
  | .sub a b => wire inputs nodes a - wire inputs nodes b
  | .mul a b => wire inputs nodes a * wire inputs nodes b

def nodeResidual (nodes : List (Node inputs fixed)) (p : Fin fixed → ℤ)
    (i : Fin nodes.length) : Expr (Variables inputs nodes.length) :=
  wire inputs nodes.length i.val - rhs nodes.length p (nodes.getD i.val (.literal 0))

def residual (nodes : List (Node inputs fixed)) (left right : ℕ) (p : Fin fixed → ℤ) :
    Fin (nodes.length+1) → Expr (Variables inputs nodes.length) :=
  Fin.cases (wire inputs nodes.length left - wire inputs nodes.length right) (nodeResidual nodes p)

def expression (nodes : List (Node inputs fixed)) (left right : ℕ) (p : Fin fixed → ℤ) :
    Expr (Variables inputs nodes.length) :=
  QuarticSyntax.sumExpressions (List.ofFn fun i =>
    let e := residual nodes left right p i
    e * e)

noncomputable def polynomial (nodes : List (Node inputs fixed)) (left right : ℕ)
    (p : Fin fixed → ℤ) : MvPolynomial (Variables inputs nodes.length) ℤ :=
  (expression nodes left right p).toPolynomial

def read {nodes : ℕ} (w : Fin nodes → ℕ) (j : ℕ) : ℤ :=
  if h : j < nodes then (w ⟨j,h⟩ : ℤ) else 0

def assignment {nodes : ℕ} (x : Fin inputs → ℕ) (w : Fin nodes → ℕ) :
    Variables inputs nodes → ℤ := Sum.elim (fun i => (x i : ℤ)) (fun i => (w i : ℤ))

@[simp] theorem eval_wire {nodes : ℕ} (x : Fin inputs → ℕ) (w : Fin nodes → ℕ) (j : ℕ) :
    (wire inputs nodes j).eval (assignment x w) = read w j := by
  unfold wire read
  split <;> rfl

theorem eval_rhs {nodes : ℕ} (p : Fin fixed → ℤ) (x : Fin inputs → ℕ)
    (w : Fin nodes → ℕ) (n : Node inputs fixed) :
    (rhs nodes p n).eval (assignment x w) =
      n.evalAt p (fun i => (x i : ℤ)) (read w) := by
  cases n <;> simp only [rhs,Expr.eval_add,Expr.eval_sub,Expr.eval_mul,
    Expr.eval_constant,Expr.eval_var,eval_wire,Node.evalAt] <;> rfl

theorem eval_nodeResidual (nodes : List (Node inputs fixed)) (p : Fin fixed → ℤ)
    (x : Fin inputs → ℕ) (w : Fin nodes.length → ℕ) (i : Fin nodes.length) :
    (nodeResidual nodes p i).eval (assignment x w) = 0 ↔
      read w i.val = (nodes.getD i.val (.literal 0)).evalAt p (fun j => (x j : ℤ)) (read w) := by
  rw [nodeResidual,Expr.eval_sub,eval_wire,eval_rhs,sub_eq_zero]

theorem expression_zero_iff (nodes : List (Node inputs fixed)) (left right : ℕ)
    (p : Fin fixed → ℤ) (v : Variables inputs nodes.length → ℤ) :
    (expression nodes left right p).eval v = 0 ↔
      ∀ i, (residual nodes left right p i).eval v = 0 :=
  CompilerSupport.sumSquares_zero_iff _ _

def witnesses (nodes : List (Node inputs fixed)) (p : Fin fixed → ℤ) (x : Fin inputs → ℕ) :
    Fin nodes.length → ℕ :=
  fun i => ((run p (fun j => (x j : ℤ)) nodes []).getD i.val 0).toNat

theorem read_witnesses (nodes : List (Node inputs fixed)) (htop : Topological nodes)
    (p : Fin fixed → ℤ) (ha : Allowed nodes p) (x : Fin inputs → ℕ) (j : ℕ)
    (hj : j < nodes.length) :
    read (witnesses nodes p x) j = (run p (fun i => (x i : ℤ)) nodes []).getD j 0 := by
  simp only [read,dif_pos hj,witnesses]
  exact Int.toNat_of_nonneg (run_nonnegative nodes htop p ha x j hj)

theorem exists_zero_iff (nodes : List (Node inputs fixed)) (htop : Topological nodes)
    (left right : ℕ) (hl : left < nodes.length) (hr : right < nodes.length)
    (p : Fin fixed → ℤ) (ha : Allowed nodes p) (x : Fin inputs → ℕ) :
    (∃ w : Fin nodes.length → ℕ,
      (expression nodes left right p).eval (assignment x w) = 0) ↔
      value nodes left p (fun i => (x i : ℤ)) = value nodes right p (fun i => (x i : ℤ)) := by
  constructor
  · rintro ⟨w,hw⟩
    have h := (expression_zero_iff nodes left right p _).mp hw
    have heq : ∀ i < nodes.length, read w i =
        (nodes.getD i (.literal 0)).evalAt p (fun j => (x j : ℤ)) (read w) := by
      intro i hi
      exact (eval_nodeResidual nodes p x w ⟨i,hi⟩).mp (h (Fin.succ ⟨i,hi⟩))
    rw [value_eq_of_node_equations p (fun i => (x i : ℤ)) nodes htop left hl _ heq,
      value_eq_of_node_equations p (fun i => (x i : ℤ)) nodes htop right hr _ heq]
    exact sub_eq_zero.mp (by simpa only [residual,Fin.cases_zero,Expr.eval_sub,eval_wire] using h 0)
  · intro h
    refine ⟨witnesses nodes p x,(expression_zero_iff nodes left right p _).mpr ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (wire inputs nodes.length left - wire inputs nodes.length right).eval _ = 0
      rw [Expr.eval_sub,eval_wire,eval_wire,read_witnesses nodes htop p ha x left hl,
        read_witnesses nodes htop p ha x right hr,sub_eq_zero]
      exact h
    · apply (eval_nodeResidual nodes p x (witnesses nodes p x) j).mpr
      rw [read_witnesses nodes htop p ha x j.val j.isLt,
        run_node_equation p (fun i => (x i : ℤ)) nodes htop j.val j.isLt]
      apply Node.evalAt_congr
      intro k hk
      exact (read_witnesses nodes htop p ha x k ((htop j k hk).trans j.isLt)).symm

theorem wire_binaryOps (inputs nodes j : ℕ) : (wire inputs nodes j).binaryOps = 0 := by
  unfold wire
  split <;> rfl

theorem rhs_binaryOps (nodes : ℕ) (p : Fin fixed → ℤ) (n : Node inputs fixed) :
    (rhs nodes p n).binaryOps ≤ 1 := by
  cases n with
  | literal z => change 0 ≤ 1; decide
  | input i => change 0 ≤ 1; decide
  | constant i => change 0 ≤ 1; decide
  | add a b | sub a b | mul a b =>
    change 1 + (wire inputs nodes a).binaryOps + (wire inputs nodes b).binaryOps ≤ 1
    rw [wire_binaryOps,wire_binaryOps]

theorem nodeResidual_binaryOps (nodes : List (Node inputs fixed)) (p : Fin fixed → ℤ)
    (i : Fin nodes.length) : (nodeResidual nodes p i).binaryOps ≤ 2 := by
  have hr := rhs_binaryOps nodes.length p (nodes.getD i.val (.literal 0))
  change 1 + (wire inputs nodes.length i.val).binaryOps + _ ≤ 2
  rw [wire_binaryOps]
  omega

/-- Nonnegative node values need half as many gate variables as signed values. -/
theorem expression_binaryOps (nodes : List (Node inputs fixed)) (left right : ℕ)
    (p : Fin fixed → ℤ) :
    (expression nodes left right p).binaryOps ≤ 6*nodes.length+4 := by
  have hrest := QuarticCost.sumExpressions_binaryOps_le
    (List.ofFn fun i => let e := nodeResidual nodes p i; e*e) (by
      intro e he
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
      have hi := nodeResidual_binaryOps nodes p i
      change 1 + _ + _ ≤ 5
      omega)
  simp only [List.length_ofFn] at hrest
  rw [expression,List.ofFn_succ]
  change 1 + (1 + (1 + (wire inputs nodes.length left).binaryOps +
    (wire inputs nodes.length right).binaryOps) +
    (1 + (wire inputs nodes.length left).binaryOps + (wire inputs nodes.length right).binaryOps)) +
    (QuarticSyntax.sumExpressions (List.ofFn fun i =>
      let e := nodeResidual nodes p i; e*e)).binaryOps ≤ _
  rw [wire_binaryOps,wire_binaryOps]
  dsimp only at hrest ⊢
  omega

theorem wire_degree (inputs nodes j : ℕ) :
    (wire inputs nodes j).toPolynomial.totalDegree ≤ 1 := by
  unfold wire
  split <;> simp [Expr.toPolynomial]

theorem rhs_degree (nodes : ℕ) (p : Fin fixed → ℤ) (n : Node inputs fixed) :
    (rhs nodes p n).toPolynomial.totalDegree ≤ 2 :=
  DAGQuartic.rhsWith_degree p Sum.inl (wire inputs nodes) (wire_degree inputs nodes) n

theorem residual_degree (nodes : List (Node inputs fixed)) (left right : ℕ)
    (p : Fin fixed → ℤ) (i : Fin (nodes.length+1)) :
    (residual nodes left right p i).toPolynomial.totalDegree ≤ 2 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact DAGQuartic.degree_sub ((wire_degree inputs nodes.length left).trans (by decide))
      ((wire_degree inputs nodes.length right).trans (by decide))
  · exact DAGQuartic.degree_sub ((wire_degree inputs nodes.length j.val).trans (by decide))
      (rhs_degree nodes.length p (nodes.getD j.val (.literal 0)))

theorem polynomial_degree (nodes : List (Node inputs fixed)) (left right : ℕ)
    (p : Fin fixed → ℤ) : (polynomial nodes left right p).totalDegree ≤ 4 :=
  CompilerSupport.sumSquares_degree_le _ 2 (residual_degree nodes left right p)

theorem variable_count (nodes : List (Node inputs fixed)) :
    Fintype.card (Variables inputs nodes.length) = inputs+nodes.length := by
  simp only [Variables,Fintype.card_sum,Fintype.card_fin]

theorem exists_polynomial_zero_iff (nodes : List (Node inputs fixed))
    (htop : Topological nodes) (left right : ℕ) (hl : left < nodes.length) (hr : right < nodes.length)
    (p : Fin fixed → ℤ) (ha : Allowed nodes p) :
    (∃ v : Variables inputs nodes.length → ℕ,
      MvPolynomial.eval (fun i => (v i : ℤ)) (polynomial nodes left right p) = 0) ↔
      ∃ x : Fin inputs → ℕ,
        value nodes left p (fun i => (x i : ℤ)) = value nodes right p (fun i => (x i : ℤ)) := by
  rw [Sum.exists_sum]
  simpa only [polynomial, Expr.eval_toPolynomial, CompilerSupport.natCast_sumRec, assignment, natAssignment] using
    (exists_congr (fun x => exists_zero_iff nodes htop left right hl hr p ha x))

end DiophantineConsistency.NaturalDAGQuartic
