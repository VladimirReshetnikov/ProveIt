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
  constructor
  · rintro ⟨hnrel,horel⟩
    by_cases hn : n = 0
    · subst n
      have ho : out = 0 := by
        have hmul : (out : ℤ) * ((out : ℤ) + 1) = 0 := by simpa using horel
        rcases mul_eq_zero.mp hmul with h0 | h1 <;> omega
      simp [ho]
    · have hni : (n : ℤ) ≠ 0 := by exact_mod_cast hn
      have hd := (mul_eq_zero.mp hnrel).resolve_left hni
      have he : out + 1 = n := by omega
      rw [←he,Nat.pred_succ]
  · intro h
    cases n with
    | zero => simp only [Nat.pred_zero] at h; simp [PredCertificate,h]
    | succ n => simp only [Nat.pred_succ] at h; simp [PredCertificate,h,Nat.cast_add]

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
    constructor
    · rintro ⟨w,hpred,hc⟩
      have hp := QuadraticNatPairing.certificate_sound hc
      change v 0 = (Nat.unpair (v 1).pred).1
      rw [←hpred,hp,Nat.unpair_pair]
    · intro h
      change v 0 = (Nat.unpair (v 1).pred).1 at h
      have hp : (v 1).pred = Nat.pair (v 0) (Nat.unpair (v 1).pred).2 := by rw [h,Nat.pair_unpair]
      obtain ⟨t,s,m,hc⟩ := QuadraticNatPairing.certificate_complete hp
      exact ⟨![(v 1).pred,(Nat.unpair (v 1).pred).2,t,s,m],rfl,hc⟩)

def treeRightRepresentation : Rep (Fin 2) (fun v => v 0 = AnnotatedCodeArithmetic.treeRight (v 1)) :=
  (System.scopedRep (a := 2) (k := 5) rightSystem).ofIff (by
    intro v
    simp only [right_holds_iff]
    change (∃ w : Fin 5 → ℕ, w 0 = (v 1).pred ∧
      QuadraticNatPairing.Certificate (w 0) (w 1) (v 0) (w 2) (w 3) (w 4)) ↔ _
    constructor
    · rintro ⟨w,hpred,hc⟩
      have hp := QuadraticNatPairing.certificate_sound hc
      change v 0 = (Nat.unpair (v 1).pred).2
      rw [←hpred,hp,Nat.unpair_pair]
    · intro h
      change v 0 = (Nat.unpair (v 1).pred).2 at h
      have hp : (v 1).pred = Nat.pair (Nat.unpair (v 1).pred).1 (v 0) := by rw [h,Nat.pair_unpair]
      obtain ⟨t,s,m,hc⟩ := QuadraticNatPairing.certificate_complete hp
      exact ⟨![(v 1).pred,(Nat.unpair (v 1).pred).1,t,s,m],rfl,hc⟩)

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
