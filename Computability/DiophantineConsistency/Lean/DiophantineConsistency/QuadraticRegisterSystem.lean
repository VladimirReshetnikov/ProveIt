import DiophantineConsistency.NaturalRegisterRelation

/-!
# Quadratic constraints attached to shared natural registers

Existing register computations are certified once by their local gate rows.
Additional quadratic rows are squared directly, without first turning the
logical constraint into another arithmetic output circuit.
-/

namespace DiophantineConsistency.QuadraticRegisterSystem

open NaturalRegisterProgram ArithmeticDAG

variable {n : ℕ}

/-- A computable degree bound needs no polynomial normalization. -/
def syntaxDegree {σ : Type*} : Expr σ → ℕ
  | .constant _ => 0
  | .var _ => 1
  | .add a b | .sub a b => max (syntaxDegree a) (syntaxDegree b)
  | .mul a b => syntaxDegree a + syntaxDegree b

theorem polynomial_degree_le {σ : Type*} (e : Expr σ) :
    e.toPolynomial.totalDegree ≤ syntaxDegree e := by
  induction e with
  | constant z =>
    change (MvPolynomial.C z : MvPolynomial σ ℤ).totalDegree ≤ 0
    rw [MvPolynomial.totalDegree_C]
  | var i => simp [Expr.toPolynomial,syntaxDegree]
  | add a b ha hb => exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max ha hb)
  | sub a b ha hb => exact (MvPolynomial.totalDegree_sub _ _).trans (max_le_max ha hb)
  | mul a b ha hb => exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add ha hb)

structure System (p : Program n) where
  rowCount : ℕ
  row : Fin rowCount → Expr (Fin n ⊕ Fin p.nodes.length)
  degree : ∀ i, (row i).toPolynomial.totalDegree ≤ 2

namespace System

variable {p : Program n}

/-- Attach supplied rows using their syntactically checked quadratic bounds. -/
def ofRows (rowCount : ℕ) (rows : Fin rowCount → Expr (Fin n ⊕ Fin p.nodes.length))
    (h : ∀ i, syntaxDegree (rows i) ≤ 2) : System p where
  rowCount := rowCount
  row := rows
  degree i := (polynomial_degree_le _).trans (h i)

def Holds (s : System p) (x : Fin n → ℕ) : Prop :=
  ∀ i, (s.row i).eval (natAssignment x (p.eval x)) = 0

def residual (s : System p) : Fin (p.nodes.length + s.rowCount) →
    Expr (Fin n ⊕ Fin p.nodes.length) :=
  Fin.addCases (NaturalDAGQuartic.nodeResidual p.nodes (fun i : Fin 0 => i.elim0)) s.row

@[simp] theorem residual_left (s : System p) (i : Fin p.nodes.length) :
    s.residual (Fin.castAdd s.rowCount i) =
      NaturalDAGQuartic.nodeResidual p.nodes (fun j : Fin 0 => j.elim0) i := by
  simp [residual]

@[simp] theorem residual_right (s : System p) (i : Fin s.rowCount) :
    s.residual (Fin.natAdd p.nodes.length i) = s.row i := by
  simp [residual]

def expression (s : System p) : Expr (Fin n ⊕ Fin p.nodes.length) :=
  QuarticSyntax.sumExpressions (List.ofFn fun i => let e := s.residual i; e * e)

theorem expression_zero_iff (s : System p) (v : Fin n ⊕ Fin p.nodes.length → ℤ) :
    s.expression.eval v = 0 ↔ ∀ i, (s.residual i).eval v = 0 :=
  CompilerSupport.sumSquares_zero_iff _ _

private theorem node_rows_iff (x : Fin n → ℕ) (w : Fin p.nodes.length → ℕ) :
    (∀ i, (NaturalDAGQuartic.nodeResidual p.nodes (fun j : Fin 0 => j.elim0) i).eval
      (natAssignment x w) = 0) ↔ w = p.eval x := by
  have ha : NaturalDAGQuartic.assignment x w = natAssignment x w := by
    funext i
    cases i <;> rfl
  constructor
  · intro h
    have heq : ∀ i < p.nodes.length, NaturalDAGQuartic.read w i =
        (p.nodes.getD i (.literal 0)).evalAt (fun j : Fin 0 => j.elim0)
          (fun j => (x j : ℤ)) (NaturalDAGQuartic.read w) := by
      intro i hi
      exact (NaturalDAGQuartic.eval_nodeResidual p.nodes _ x w ⟨i,hi⟩).mp (by rw [ha]; exact h ⟨i,hi⟩)
    have hc := ArithmeticDAG.run_eq_of_node_equations (fun j : Fin 0 => j.elim0)
      (fun j => (x j : ℤ)) p.nodes p.topological (NaturalDAGQuartic.read w) heq
    funext i
    apply Int.ofNat.inj
    change (w i : ℤ) = (p.eval x i : ℤ)
    rw [Program.cast_eval]
    simpa only [ArithmeticDAG.value,NaturalDAGQuartic.read,dif_pos i.isLt] using (hc i.val i.isLt).symm
  · rintro rfl
    intro i
    apply (NaturalDAGQuartic.eval_nodeResidual p.nodes _ x (p.eval x) i).mpr
    have hr (j : ℕ) (hj : j < p.nodes.length) :
        NaturalDAGQuartic.read (p.eval x) j =
          (ArithmeticDAG.run (fun k : Fin 0 => k.elim0) (fun k => (x k : ℤ)) p.nodes []).getD j 0 :=
      NaturalDAGQuartic.read_witnesses p.nodes p.topological _ p.allowed x j hj
    rw [hr i.val i.isLt,ArithmeticDAG.run_node_equation _ _ p.nodes p.topological i.val i.isLt]
    apply Node.evalAt_congr
    intro j hj
    exact (hr j ((p.topological i j hj).trans i.isLt)).symm

def representation (s : System p) : Rep (Fin n) s.Holds where
  witnessCount := p.nodes.length
  expression := s.expression
  correct := by
    intro x
    constructor
    · intro h
      refine ⟨p.eval x,(s.expression_zero_iff _).mpr ?_⟩
      intro i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [residual_left] using (node_rows_iff x (p.eval x)).mpr rfl j
      · intro j
        simpa only [residual_right] using h j
    · rintro ⟨w,hw⟩
      have hr := (s.expression_zero_iff _).mp hw
      have hg : w = p.eval x := (node_rows_iff x w).mp (fun i => by
        simpa only [residual_left] using hr (Fin.castAdd s.rowCount i))
      intro i
      simpa only [hg,residual_right] using hr (Fin.natAdd p.nodes.length i)

@[simp] theorem representation_witnessCount (s : System p) :
    s.representation.witnessCount = p.nodes.length := rfl

theorem residual_degree (s : System p) (i : Fin (p.nodes.length + s.rowCount)) :
    (s.residual i).toPolynomial.totalDegree ≤ 2 := by
  refine Fin.addCases (fun j : Fin p.nodes.length => ?_) (fun j : Fin s.rowCount => ?_) i
  · rw [residual_left]
    simpa only [NaturalDAGQuartic.residual,Fin.cases_succ] using
      NaturalDAGQuartic.residual_degree p.nodes 0 0 (fun i : Fin 0 => i.elim0) j.succ
  · rw [residual_right]
    exact s.degree j

theorem expression_degree (s : System p) : s.expression.toPolynomial.totalDegree ≤ 4 :=
  CompilerSupport.sumSquares_degree_le _ 2 s.residual_degree

/-- Move the supplied auxiliary-input block into the natural witnesses. -/
def scopedRep {a k : ℕ} {p : Program (a+k)} (s : System p) :
    Rep (Fin a) (fun v => ∃ w : Fin k → ℕ, s.Holds (Fin.addCases v w)) :=
  (((s.representation.reindex (NaturalRegisterRelation.splitIndex a k)).existsBlock).ofIff
    (fun v => by simp only [NaturalRegisterRelation.merge_split]))

@[simp] theorem scopedRep_witnessCount {a k : ℕ} {p : Program (a+k)} (s : System p) :
    s.scopedRep.witnessCount = k + p.nodes.length := rfl

theorem scopedRep_degree {a k : ℕ} {p : Program (a+k)} (s : System p) :
    s.scopedRep.expression.toPolynomial.totalDegree ≤ 4 := by
  simp only [scopedRep,Rep.ofIff,Rep.existsBlock,Rep.reindex,NaturalRegisterRelation.rename_toPolynomial]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    ((MvPolynomial.totalDegree_rename_le _ _).trans s.expression_degree)

end System
end DiophantineConsistency.QuadraticRegisterSystem
