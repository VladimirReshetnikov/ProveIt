import DiophantineConsistency.QuadraticRegisterComposition
import DiophantineConsistency.QuadraticNatPairing
import DiophantineConsistency.AnnotatedCodeArithmetic

/-! # Compositional quadratic graphs for actual annotated-checker tree operations -/

namespace DiophantineConsistency.QuadraticTreeCodeGraphs

open NaturalRegisterProgram QuadraticRegisterSystem AnnotatedCodeArithmetic

attribute [local irreducible] Nat.unpair

def PredCertificate (out n : ℕ) : Prop :=
  (n : ℤ) * ((out : ℤ) + 1 - n) = 0 ∧ (out : ℤ) * ((out : ℤ) + 1 - n) = 0

theorem pred_certificate_iff (out n : ℕ) : PredCertificate out n ↔ out = n.pred := by
  cases n with
  | zero =>
    simp only [PredCertificate, Nat.cast_zero, Nat.pred_zero, mul_eq_zero,
      Int.natCast_eq_zero, true_or, true_and, sub_zero]
    omega
  | succ n =>
    simp only [PredCertificate, Nat.cast_succ, Nat.pred_succ, mul_eq_zero,
      Int.natCast_eq_zero]
    omega

def predProgram : Program 2 := .empty
private def predInput (i : Fin 2) : Expr (Fin 2 ⊕ Fin predProgram.nodes.length) := .var (.inl i)

def predRows : Fin 2 → Expr (Fin 2 ⊕ Fin predProgram.nodes.length) :=
  ![predInput 1 * (predInput 0 + 1 - predInput 1),
    predInput 0 * (predInput 0 + 1 - predInput 1)]

def predSystem : System predProgram := System.ofRows 2 predRows (by intro i; fin_cases i <;> decide)

theorem pred_holds_iff (x : Fin 2 → ℕ) : predSystem.Holds x ↔ x 0 = (x 1).pred := by
  have he : predSystem.Holds x ↔ PredCertificate (x 0) (x 1) := by
    simp [System.Holds,predSystem,System.ofRows,predRows,predInput,Expr.eval,natAssignment,
      PredCertificate,Fin.forall_fin_succ]
  exact he.trans (pred_certificate_iff _ _)

/-- One preallocated shared context: output, code, predecessor, other pair
component, branch bit, branch slack, and maximum pair component. -/
def program : Program 7 := .empty

private def predPorts : Fin 2 → Slot program := ![.inl 2,.inl 1]
private def leftPorts : Fin 6 → Slot program :=
  ![.inl 0,.inl 2,.inl 3,.inl 4,.inl 5,.inl 6]
private def rightPorts : Fin 6 → Slot program :=
  ![.inl 3,.inl 2,.inl 0,.inl 4,.inl 5,.inl 6]

def leftSystem : System program :=
  (predSystem.instantiate program predPorts).conjunction
    ((QuadraticNatPairing.system 0 2).instantiate program leftPorts)

def rightSystem : System program :=
  (predSystem.instantiate program predPorts).conjunction
    ((QuadraticNatPairing.system 0 2).instantiate program rightPorts)

theorem left_holds_iff (x : Fin 7 → ℕ) : leftSystem.Holds x ↔
    x 2 = (x 1).pred ∧ QuadraticNatPairing.Certificate (x 2) (x 0) (x 3) (x 4) (x 5) (x 6) := by
  rw [leftSystem,System.conjunction_holds,System.instantiate_holds,System.instantiate_holds]
  exact and_congr (pred_holds_iff _) (QuadraticNatPairing.holds_iff 0 2 _)

theorem right_holds_iff (x : Fin 7 → ℕ) : rightSystem.Holds x ↔
    x 2 = (x 1).pred ∧ QuadraticNatPairing.Certificate (x 2) (x 3) (x 0) (x 4) (x 5) (x 6) := by
  rw [rightSystem,System.conjunction_holds,System.instantiate_holds,System.instantiate_holds]
  exact and_congr (pred_holds_iff _) (QuadraticNatPairing.holds_iff 0 2 _)

def treeLeftRepresentation : Rep (Fin 2) (fun v => v 0 = AnnotatedCodeArithmetic.treeLeft (v 1)) :=
  (System.scopedRep (a := 2) (k := 5) leftSystem).ofIff (by
    intro v
    simp only [left_holds_iff]
    change (∃ w : Fin 5 → ℕ, w 0 = (v 1).pred ∧
      QuadraticNatPairing.Certificate (w 0) (v 0) (w 1) (w 2) (w 3) (w 4)) ↔ _
    simp [Fin.exists_fin_succ_pi, exists_and_left,
      QuadraticNatPairing.exists_certificate_iff, GraphRep.exists_pair_right_iff,
      AnnotatedCodeArithmetic.treeLeft])

def treeRightRepresentation : Rep (Fin 2) (fun v => v 0 = AnnotatedCodeArithmetic.treeRight (v 1)) :=
  (System.scopedRep (a := 2) (k := 5) rightSystem).ofIff (by
    intro v
    simp only [right_holds_iff]
    change (∃ w : Fin 5 → ℕ, w 0 = (v 1).pred ∧
      QuadraticNatPairing.Certificate (w 0) (w 1) (v 0) (w 2) (w 3) (w 4)) ↔ _
    simp [Fin.exists_fin_succ_pi, exists_and_left,
      QuadraticNatPairing.exists_certificate_iff, GraphRep.exists_pair_left_iff,
      AnnotatedCodeArithmetic.treeRight])

private def graphIndex : Fin 2 → Option (Fin 1) := Fin.cases none (fun _ => some 0)

def treeLeft : GraphRep (fun v : Fin 1 → ℕ => AnnotatedCodeArithmetic.treeLeft (v 0)) :=
  (treeLeftRepresentation.reindex graphIndex).ofIff (fun _ => Iff.rfl)

def treeRight : GraphRep (fun v : Fin 1 → ℕ => AnnotatedCodeArithmetic.treeRight (v 0)) :=
  (treeRightRepresentation.reindex graphIndex).ofIff (fun _ => Iff.rfl)

/-- For this exact second projection, the nil guard agrees with its zero value. -/
theorem listTail_eq_treeRight (code : ℕ) :
    AnnotatedCodeArithmetic.listTail code = AnnotatedCodeArithmetic.treeRight code := by
  by_cases h : code = 0
  · subst code
    simp [AnnotatedCodeArithmetic.listTail,AnnotatedCodeArithmetic.treeRight,Nat.unpair_zero]
  · simp only [AnnotatedCodeArithmetic.listTail,if_neg h,AnnotatedCodeArithmetic.treeRight]

def listTail : GraphRep (fun v : Fin 1 → ℕ => AnnotatedCodeArithmetic.listTail (v 0)) :=
  treeRight.ofIff (fun v => by simp only [listTail_eq_treeRight])

@[simp] theorem treeLeft_witnessCount : treeLeft.witnessCount = 5 := rfl
@[simp] theorem treeRight_witnessCount : treeRight.witnessCount = 5 := rfl
@[simp] theorem listTail_witnessCount : listTail.witnessCount = 5 := rfl

theorem treeLeft_binaryOps : treeLeft.expression.binaryOps = 62 := by decide
theorem treeRight_binaryOps : treeRight.expression.binaryOps = 62 := by decide
theorem listTail_binaryOps : listTail.expression.binaryOps = 62 := by decide

theorem treeLeft_degree : treeLeft.expression.toPolynomial.totalDegree ≤ 4 := by
  simp only [treeLeft,Rep.ofIff,Rep.reindex,NaturalRegisterRelation.rename_toPolynomial]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (System.scopedRep_degree (a := 2) (k := 5) leftSystem)

theorem treeRight_degree : treeRight.expression.toPolynomial.totalDegree ≤ 4 := by
  simp only [treeRight,Rep.ofIff,Rep.reindex,NaturalRegisterRelation.rename_toPolynomial]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (System.scopedRep_degree (a := 2) (k := 5) rightSystem)

theorem listTail_degree : listTail.expression.toPolynomial.totalDegree ≤ 4 := treeRight_degree

end DiophantineConsistency.QuadraticTreeCodeGraphs
