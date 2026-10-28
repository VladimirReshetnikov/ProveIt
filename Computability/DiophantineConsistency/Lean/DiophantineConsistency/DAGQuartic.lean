import DiophantineConsistency.ArithmeticDAGSemantics
import DiophantineConsistency.QuarticCost
import DiophantineConsistency.CompilerSupport

/-!
# A quartic compiler that preserves arithmetic-circuit sharing

Each stored circuit node is represented by two natural variables, whose
difference is its integer value. Local quadratic equations and the output
equation are squared and added. The construction never expands the circuit
into an arithmetic expression tree. It applies to arbitrary integer constants
and subtraction nodes, without requiring nonnegative intermediate values.
-/

namespace DiophantineConsistency.DAGQuartic

open ArithmeticDAG

variable {inputs fixed : ℕ}

abbrev Variables (inputs nodes : ℕ) := Fin inputs ⊕ (Fin nodes ⊕ Fin nodes)

/-- Every stored value has a positive and a negative natural part. -/
def wire (inputs nodes j : ℕ) : Expr (Variables inputs nodes) :=
  if h : j < nodes then
    .var (.inr (.inl ⟨j,h⟩)) - .var (.inr (.inr ⟨j,h⟩))
  else .constant 0

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

/-- The first residual is the output; all other residuals are local nodes. -/
def residual (nodes : List (Node inputs fixed)) (output : ℕ) (p : Fin fixed → ℤ) :
    Fin (nodes.length+1) → Expr (Variables inputs nodes.length) :=
  Fin.cases (wire inputs nodes.length output) (nodeResidual nodes p)

def expression (nodes : List (Node inputs fixed)) (output : ℕ) (p : Fin fixed → ℤ) :
    Expr (Variables inputs nodes.length) :=
  QuarticSyntax.sumExpressions (List.ofFn fun i =>
    let e := residual nodes output p i
    e * e)

noncomputable def polynomial (nodes : List (Node inputs fixed)) (output : ℕ)
    (p : Fin fixed → ℤ) : MvPolynomial (Variables inputs nodes.length) ℤ :=
  (expression nodes output p).toPolynomial

def signedRead {nodes : ℕ} (w : Fin nodes ⊕ Fin nodes → ℕ) (j : ℕ) : ℤ :=
  if h : j < nodes then (w (.inl ⟨j,h⟩) : ℤ) - w (.inr ⟨j,h⟩) else 0

def assignment {nodes : ℕ} (x : Fin inputs → ℕ) (w : Fin nodes ⊕ Fin nodes → ℕ) :
    Variables inputs nodes → ℤ :=
  Sum.elim (fun i => (x i : ℤ)) (fun i => (w i : ℤ))

@[simp] theorem eval_wire {nodes : ℕ} (x : Fin inputs → ℕ)
    (w : Fin nodes ⊕ Fin nodes → ℕ) (j : ℕ) :
    (wire inputs nodes j).eval (assignment x w) = signedRead w j := by
  unfold wire signedRead
  split <;> rfl

theorem eval_rhs {nodes : ℕ} (p : Fin fixed → ℤ) (x : Fin inputs → ℕ)
    (w : Fin nodes ⊕ Fin nodes → ℕ) (n : Node inputs fixed) :
    (rhs nodes p n).eval (assignment x w) =
      n.evalAt p (fun i => (x i : ℤ)) (signedRead w) := by
  cases n <;> simp only [rhs,Expr.eval_add,Expr.eval_sub,Expr.eval_mul,
    Expr.eval_constant,Expr.eval_var,eval_wire,Node.evalAt] <;> rfl

theorem eval_nodeResidual (nodes : List (Node inputs fixed)) (p : Fin fixed → ℤ)
    (x : Fin inputs → ℕ) (w : Fin nodes.length ⊕ Fin nodes.length → ℕ)
    (i : Fin nodes.length) :
    (nodeResidual nodes p i).eval (assignment x w) = 0 ↔
      signedRead w i.val = (nodes.getD i.val (.literal 0)).evalAt p
        (fun j => (x j : ℤ)) (signedRead w) := by
  rw [nodeResidual,Expr.eval_sub,eval_wire,eval_rhs,sub_eq_zero]

theorem expression_zero_iff (nodes : List (Node inputs fixed)) (output : ℕ)
    (p : Fin fixed → ℤ) (v : Variables inputs nodes.length → ℤ) :
    (expression nodes output p).eval v = 0 ↔
      ∀ i, (residual nodes output p i).eval v = 0 :=
  CompilerSupport.sumSquares_zero_iff _ _

/-- An arbitrary signed circuit evaluation supplies the gate witnesses. -/
def witnesses (nodes : List (Node inputs fixed)) (p : Fin fixed → ℤ) (x : Fin inputs → ℕ) :
    Fin nodes.length ⊕ Fin nodes.length → ℕ :=
  Sum.elim (fun i => ((run p (fun j => (x j : ℤ)) nodes []).getD i.val 0).toNat)
    (fun i => (-((run p (fun j => (x j : ℤ)) nodes []).getD i.val 0)).toNat)

theorem signedRead_witnesses (nodes : List (Node inputs fixed)) (p : Fin fixed → ℤ)
    (x : Fin inputs → ℕ) (j : ℕ) (hj : j < nodes.length) :
    signedRead (witnesses nodes p x) j = (run p (fun i => (x i : ℤ)) nodes []).getD j 0 := by
  simp only [signedRead,dif_pos hj,witnesses,Sum.elim_inl,Sum.elim_inr]
  omega

/-- Existential gate witnesses add no semantic premise. Topology is essential. -/
theorem exists_zero_iff (nodes : List (Node inputs fixed)) (htop : Topological nodes)
    (output : ℕ) (ho : output < nodes.length) (p : Fin fixed → ℤ) (x : Fin inputs → ℕ) :
    (∃ w : Fin nodes.length ⊕ Fin nodes.length → ℕ,
      (expression nodes output p).eval (assignment x w) = 0) ↔
      value nodes output p (fun i => (x i : ℤ)) = 0 := by
  constructor
  · rintro ⟨w,hw⟩
    have h := (expression_zero_iff nodes output p _).mp hw
    have heq : ∀ i < nodes.length, signedRead w i =
        (nodes.getD i (.literal 0)).evalAt p (fun j => (x j : ℤ)) (signedRead w) := by
      intro i hi
      exact (eval_nodeResidual nodes p x w ⟨i,hi⟩).mp (h (Fin.succ ⟨i,hi⟩))
    rw [value_eq_of_node_equations p (fun i => (x i : ℤ)) nodes htop output ho _ heq]
    exact (eval_wire x w output).symm.trans (h 0)
  · intro h
    refine ⟨witnesses nodes p x,(expression_zero_iff nodes output p _).mpr ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (wire inputs nodes.length output).eval _ = 0
      rw [eval_wire,signedRead_witnesses nodes p x output ho]
      exact h
    · apply (eval_nodeResidual nodes p x (witnesses nodes p x) j).mpr
      rw [signedRead_witnesses nodes p x j.val j.isLt,
        run_node_equation p (fun i => (x i : ℤ)) nodes htop j.val j.isLt]
      apply Node.evalAt_congr
      intro k hk
      exact (signedRead_witnesses nodes p x k
        ((htop j k hk).trans j.isLt)).symm

theorem wire_binaryOps (inputs nodes j : ℕ) : (wire inputs nodes j).binaryOps ≤ 1 := by
  unfold wire
  split
  · change 1+0+0 ≤ 1
    omega
  · change 0 ≤ 1
    omega

theorem rhs_binaryOps (nodes : ℕ) (p : Fin fixed → ℤ) (n : Node inputs fixed) :
    (rhs nodes p n).binaryOps ≤ 3 := by
  cases n with
  | literal z => simp [rhs,Expr.binaryOps]
  | input i => simp [rhs,Expr.binaryOps]
  | constant i => simp [rhs,Expr.binaryOps]
  | add a b | sub a b | mul a b =>
    have ha := wire_binaryOps inputs nodes a
    have hb := wire_binaryOps inputs nodes b
    change 1 + _ + _ ≤ 3
    omega

theorem nodeResidual_binaryOps (nodes : List (Node inputs fixed)) (p : Fin fixed → ℤ)
    (i : Fin nodes.length) : (nodeResidual nodes p i).binaryOps ≤ 5 := by
  have hw := wire_binaryOps inputs nodes.length i.val
  have hr := rhs_binaryOps nodes.length p (nodes.getD i.val (.literal 0))
  change 1 + _ + _ ≤ 5
  omega

private theorem sumExpressions_cost {σ : Type*} (es : List (Expr σ)) (b : ℕ)
    (h : ∀ e ∈ es, e.binaryOps ≤ b) :
    (QuarticSyntax.sumExpressions es).binaryOps ≤ (b+1)*es.length := by
  induction es with
  | nil => simp [QuarticSyntax.sumExpressions,Expr.binaryOps]
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun e he => h e (by simp [he]))
    change 1 + e.binaryOps + (QuarticSyntax.sumExpressions es).binaryOps ≤ _
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

/-- A linear syntax-tree bound; earlier node computations are never copied. -/
theorem expression_binaryOps (nodes : List (Node inputs fixed)) (output : ℕ)
    (p : Fin fixed → ℤ) :
    (expression nodes output p).binaryOps ≤ 12*nodes.length+4 := by
  have hout := wire_binaryOps inputs nodes.length output
  have hrest := sumExpressions_cost
    (List.ofFn fun i => let e := nodeResidual nodes p i; e*e) 11 (by
      intro e he
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
      have hi := nodeResidual_binaryOps nodes p i
      change 1 + _ + _ ≤ 11
      omega)
  simp only [List.length_ofFn] at hrest
  rw [expression,List.ofFn_succ]
  change 1 + (1 + (wire inputs nodes.length output).binaryOps +
    (wire inputs nodes.length output).binaryOps) +
    (QuarticSyntax.sumExpressions (List.ofFn fun i =>
      let e := nodeResidual nodes p i; e*e)).binaryOps ≤ _
  dsimp only at hrest ⊢
  omega

theorem degree_sub {σ : Type*} {p q : MvPolynomial σ ℤ} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) : (p-q).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_sub _ _).trans (max_le hp hq)

private theorem degree_add {σ : Type*} {p q : MvPolynomial σ ℤ} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) : (p+q).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_add _ _).trans (max_le hp hq)

theorem wire_degree (inputs nodes j : ℕ) :
    (wire inputs nodes j).toPolynomial.totalDegree ≤ 1 := by
  unfold wire
  split
  · exact degree_sub (by simp [Expr.toPolynomial]) (by simp [Expr.toPolynomial])
  · simp [Expr.toPolynomial]

def rhsWith {σ : Type*} (p : Fin fixed → ℤ) (input : Fin inputs → σ)
    (wire : ℕ → Expr σ) : Node inputs fixed → Expr σ
  | .literal z => .constant z
  | .input i => .var (input i)
  | .constant i => .constant (p i)
  | .add a b => wire a + wire b
  | .sub a b => wire a - wire b
  | .mul a b => wire a * wire b

/-- A quadratic bound independent of how the circuit wires are represented. -/
theorem rhsWith_degree {σ : Type*} (p : Fin fixed → ℤ) (input : Fin inputs → σ)
    (wire : ℕ → Expr σ) (hw : ∀ j, (wire j).toPolynomial.totalDegree ≤ 1)
    (n : Node inputs fixed) : (rhsWith p input wire n).toPolynomial.totalDegree ≤ 2 := by
  cases n with
  | literal z =>
    change (MvPolynomial.C z : MvPolynomial σ ℤ).totalDegree ≤ 2
    rw [MvPolynomial.totalDegree_C]
    omega
  | input i => simp [rhsWith,Expr.toPolynomial]
  | constant i =>
    change (MvPolynomial.C (p i) : MvPolynomial σ ℤ).totalDegree ≤ 2
    rw [MvPolynomial.totalDegree_C]
    omega
  | add a b =>
    exact degree_add ((hw a).trans (by decide))
      ((hw b).trans (by decide))
  | sub a b =>
    exact degree_sub ((hw a).trans (by decide))
      ((hw b).trans (by decide))
  | mul a b =>
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (hw a) (hw b))


theorem rhs_degree (nodes : ℕ) (p : Fin fixed → ℤ) (n : Node inputs fixed) :
    (rhs nodes p n).toPolynomial.totalDegree ≤ 2 :=
  rhsWith_degree p Sum.inl (wire inputs nodes) (wire_degree inputs nodes) n

theorem residual_degree (nodes : List (Node inputs fixed)) (output : ℕ)
    (p : Fin fixed → ℤ) (i : Fin (nodes.length+1)) :
    (residual nodes output p i).toPolynomial.totalDegree ≤ 2 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (wire_degree inputs nodes.length output).trans (by decide)
  · exact degree_sub ((wire_degree inputs nodes.length j.val).trans (by decide))
      (rhs_degree nodes.length p (nodes.getD j.val (.literal 0)))

theorem polynomial_degree (nodes : List (Node inputs fixed)) (output : ℕ)
    (p : Fin fixed → ℤ) : (polynomial nodes output p).totalDegree ≤ 4 :=
  CompilerSupport.sumSquares_degree_le _ 2 (residual_degree nodes output p)

/-- The number of natural variables, charging both parts of every node. -/
theorem variable_count (nodes : List (Node inputs fixed)) :
    Fintype.card (Variables inputs nodes.length) = inputs+2*nodes.length := by
  simp only [Variables,Fintype.card_sum,Fintype.card_fin]
  omega

theorem exists_polynomial_zero_iff (nodes : List (Node inputs fixed))
    (htop : Topological nodes) (output : ℕ) (ho : output < nodes.length)
    (p : Fin fixed → ℤ) :
    (∃ v : Variables inputs nodes.length → ℕ,
      MvPolynomial.eval (fun i => (v i : ℤ)) (polynomial nodes output p) = 0) ↔
      ∃ x : Fin inputs → ℕ, value nodes output p (fun i => (x i : ℤ)) = 0 := by
  rw [Sum.exists_sum]
  simpa only [polynomial, Expr.eval_toPolynomial, CompilerSupport.natCast_sumRec, assignment, natAssignment] using
    (exists_congr (fun x => exists_zero_iff nodes htop output ho p x))

end DiophantineConsistency.DAGQuartic
