import DiophantineConsistency.NaturalDAGQuartic

/-!
# Natural arithmetic registers before expression inlining

A program stores a checked topological DAG. Each operation appends one register
and reads earlier registers by finite index. Reusing a register copies only its
index, while the quartic expression is constructed once at the final boundary.
-/

namespace DiophantineConsistency.NaturalRegisterProgram

open ArithmeticDAG

/-- An operation with references restricted to the existing register bank. -/
inductive Op (inputs registers : ℕ) where
  | literal (value : ℕ)
  | input (index : Fin inputs)
  | add (left right : Fin registers)
  | mul (left right : Fin registers)
  deriving DecidableEq, Repr

namespace Op

variable {inputs registers : ℕ}

def toNode : Op inputs registers → Node inputs 0
  | .literal n => .literal (n : ℤ)
  | .input i => .input i
  | .add a b => .add a.val b.val
  | .mul a b => .mul a.val b.val

def eval (x : Fin inputs → ℕ) (values : Fin registers → ℕ) : Op inputs registers → ℕ
  | .literal n => n
  | .input i => x i
  | .add a b => values a + values b
  | .mul a b => values a * values b

theorem dependency_lt (o : Op inputs registers) (j : ℕ) (hj : j ∈ o.toNode.dependencies) :
    j < registers := by
  cases o with
  | literal n | input n => simp [toNode,Node.dependencies] at hj
  | add a b | mul a b =>
    simp [toNode,Node.dependencies] at hj
    rcases hj with rfl | rfl
    · exact a.isLt
    · exact b.isLt

theorem allowed (o : Op inputs registers) :
    NaturalDAGQuartic.NodeAllowed (fun i : Fin 0 => i.elim0) o.toNode := by
  cases o <;> simp [toNode,NaturalDAGQuartic.NodeAllowed]

end Op

/-- All proof fields certify explicit data; none supplies missing program data. -/
structure Program (inputs : ℕ) where
  nodes : List (Node inputs 0)
  topological : Topological nodes
  allowed : NaturalDAGQuartic.Allowed nodes (fun i : Fin 0 => i.elim0)

namespace Program

variable {inputs : ℕ}

/-- No registers and no operations. -/
def empty : Program inputs where
  nodes := []
  topological := by intro i; exact i.elim0
  allowed := by intro i; exact i.elim0

/-- Append one local operation; the earlier register bank is stored once. -/
def push (p : Program inputs) (o : Op inputs p.nodes.length) : Program inputs where
  nodes := p.nodes ++ [o.toNode]
  topological := by
    intro i j hj
    by_cases hi : i.val < p.nodes.length
    · rw [List.getD_append _ _ _ _ hi] at hj
      exact p.topological ⟨i.val,hi⟩ j hj
    · have he : i.val = p.nodes.length := by
        have h := i.isLt
        simp only [List.length_append,List.length_singleton] at h
        omega
      rw [he,List.getD_append_right _ _ _ _ (by omega),Nat.sub_self] at hj
      simpa only [he] using o.dependency_lt j hj
  allowed := by
    intro i
    by_cases hi : i.val < p.nodes.length
    · rw [List.getD_append _ _ _ _ hi]
      exact p.allowed ⟨i.val,hi⟩
    · have he : i.val = p.nodes.length := by
        have h := i.isLt
        simp only [List.length_append,List.length_singleton] at h
        omega
      change NaturalDAGQuartic.NodeAllowed _ ((p.nodes ++ [o.toNode]).getD i.val (.literal 0))
      rw [he,List.getD_append_right _ _ _ _ (by omega),Nat.sub_self]
      exact o.allowed

@[simp] theorem nodes_push (p : Program inputs) (o : Op inputs p.nodes.length) :
    (p.push o).nodes = p.nodes ++ [o.toNode] := rfl

@[simp] theorem length_push (p : Program inputs) (o : Op inputs p.nodes.length) :
    (p.push o).nodes.length = p.nodes.length + 1 := by simp [push]

/-- Earlier register indices remain valid after an append. -/
def old (p : Program inputs) (o : Op inputs p.nodes.length) (i : Fin p.nodes.length) :
    Fin (p.push o).nodes.length := ⟨i.val,by simpa only [length_push] using Nat.lt_succ_of_lt i.isLt⟩

/-- The appended operation's register. -/
def last (p : Program inputs) (o : Op inputs p.nodes.length) : Fin (p.push o).nodes.length :=
  ⟨p.nodes.length,by simpa only [length_push] using Nat.lt_succ_self p.nodes.length⟩

/-- Natural semantics are extracted from the proved nonnegative circuit values. -/
def eval (p : Program inputs) (x : Fin inputs → ℕ) (i : Fin p.nodes.length) : ℕ :=
  (ArithmeticDAG.value p.nodes i.val (fun j : Fin 0 => j.elim0) (fun j => (x j : ℤ))).toNat

@[simp] theorem cast_eval (p : Program inputs) (x : Fin inputs → ℕ) (i : Fin p.nodes.length) :
    (p.eval x i : ℤ) =
      ArithmeticDAG.value p.nodes i.val (fun j : Fin 0 => j.elim0) (fun j => (x j : ℤ)) :=
  Int.toNat_of_nonneg (NaturalDAGQuartic.run_nonnegative p.nodes p.topological _ p.allowed x i.val i.isLt)

private theorem eval_operation (p : Program inputs) (o : Op inputs p.nodes.length)
    (x : Fin inputs → ℕ) :
    o.toNode.eval (fun j : Fin 0 => j.elim0) (fun j => (x j : ℤ))
      (ArithmeticDAG.run (fun j : Fin 0 => j.elim0) (fun j => (x j : ℤ)) p.nodes []) =
        (o.eval x (p.eval x) : ℤ) := by
  cases o <;> simp only [Op.toNode,Op.eval,Node.eval,Nat.cast_add,Nat.cast_mul,cast_eval,
    ArithmeticDAG.value,Int.cast_id]

@[simp] theorem eval_old (p : Program inputs) (o : Op inputs p.nodes.length)
    (x : Fin inputs → ℕ) (i : Fin p.nodes.length) :
    (p.push o).eval x (p.old o i) = p.eval x i := by
  apply Int.ofNat.inj
  change (((p.push o).eval x (p.old o i) : ℕ) : ℤ) = (p.eval x i : ℤ)
  rw [cast_eval,cast_eval]
  change (ArithmeticDAG.run _ _ (p.nodes ++ [o.toNode]) []).getD i.val 0 =
    (ArithmeticDAG.run _ _ p.nodes []).getD i.val 0
  rw [ArithmeticDAG.run_append,ArithmeticDAG.run,ArithmeticDAG.run]
  apply List.getD_append
  simpa only [ArithmeticDAG.run_length,List.length_nil,Nat.add_zero] using i.isLt

@[simp] theorem eval_last (p : Program inputs) (o : Op inputs p.nodes.length)
    (x : Fin inputs → ℕ) : (p.push o).eval x (p.last o) = o.eval x (p.eval x) := by
  apply Int.ofNat.inj
  change (((p.push o).eval x (p.last o) : ℕ) : ℤ) = (o.eval x (p.eval x) : ℤ)
  rw [cast_eval]
  change (ArithmeticDAG.run _ _ (p.nodes ++ [o.toNode]) []).getD p.nodes.length 0 = _
  rw [ArithmeticDAG.run_append,ArithmeticDAG.run,ArithmeticDAG.run]
  rw [List.getD_append_right _ _ _ _ (by
    simp only [ArithmeticDAG.run_length,List.length_nil,Nat.add_zero]
    exact le_rfl)]
  simp only [ArithmeticDAG.run_length,List.length_nil,Nat.add_zero,Nat.sub_self,List.getD_cons_zero]
  exact eval_operation p o x

/-- A register carries a semantic specification without copying its computation. -/
def Realizes (p : Program inputs) (i : Fin p.nodes.length)
    (f : (Fin inputs → ℕ) → ℕ) : Prop := ∀ x, p.eval x i = f x

theorem realizes_old (p : Program inputs) (o : Op inputs p.nodes.length)
    (i : Fin p.nodes.length) {f : (Fin inputs → ℕ) → ℕ} (hi : p.Realizes i f) :
    (p.push o).Realizes (p.old o i) f := by
  intro x
  exact (p.eval_old o x i).trans (hi x)

theorem realizes_literal (p : Program inputs) (n : ℕ) :
    (p.push (.literal n)).Realizes (p.last (.literal n)) (fun _ => n) := by
  intro x
  exact p.eval_last (.literal n) x

theorem realizes_input (p : Program inputs) (i : Fin inputs) :
    (p.push (.input i)).Realizes (p.last (.input i)) (fun x => x i) := by
  intro x
  exact p.eval_last (.input i) x

theorem realizes_add (p : Program inputs) (i j : Fin p.nodes.length)
    {f g : (Fin inputs → ℕ) → ℕ} (hi : p.Realizes i f) (hj : p.Realizes j g) :
    (p.push (.add i j)).Realizes (p.last (.add i j)) (fun x => f x + g x) := by
  intro x
  exact (p.eval_last (.add i j) x).trans (congrArg₂ (· + ·) (hi x) (hj x))

theorem realizes_mul (p : Program inputs) (i j : Fin p.nodes.length)
    {f g : (Fin inputs → ℕ) → ℕ} (hi : p.Realizes i f) (hj : p.Realizes j g) :
    (p.push (.mul i j)).Realizes (p.last (.mul i j)) (fun x => f x * g x) := by
  intro x
  exact (p.eval_last (.mul i j) x).trans (congrArg₂ (· * ·) (hi x) (hj x))

/-- Compile two selected outputs to a single quartic, retaining all DAG sharing. -/
def equalityRep (p : Program inputs) (left right : Fin p.nodes.length) :
    Rep (Fin inputs) (fun x => p.eval x left = p.eval x right) where
  witnessCount := p.nodes.length
  expression := NaturalDAGQuartic.expression p.nodes left.val right.val (fun i : Fin 0 => i.elim0)
  correct := by
    intro x
    have h := NaturalDAGQuartic.exists_zero_iff p.nodes p.topological left.val right.val
      left.isLt right.isLt (fun i : Fin 0 => i.elim0) p.allowed x
    rw [←cast_eval p x left,←cast_eval p x right,Int.natCast_inj] at h
    have he (w : Fin p.nodes.length → ℕ) : NaturalDAGQuartic.assignment x w = natAssignment x w := by
      funext i
      cases i <;> rfl
    simpa only [he] using h.symm

@[simp] theorem equalityRep_witnessCount (p : Program inputs) (left right : Fin p.nodes.length) :
    (p.equalityRep left right).witnessCount = p.nodes.length := rfl

theorem equalityRep_binaryOps (p : Program inputs) (left right : Fin p.nodes.length) :
    (p.equalityRep left right).expression.binaryOps ≤ 6 * p.nodes.length + 4 :=
  NaturalDAGQuartic.expression_binaryOps _ _ _ _

theorem equalityRep_degree (p : Program inputs) (left right : Fin p.nodes.length) :
    (p.equalityRep left right).expression.toPolynomial.totalDegree ≤ 4 :=
  NaturalDAGQuartic.polynomial_degree _ _ _ _

end Program

end DiophantineConsistency.NaturalRegisterProgram
