import DiophantineConsistency.QuadraticTreeCodeGraphs

/-! # A guarded quadratic graph for the actual annotated-checker list head -/

namespace DiophantineConsistency.QuadraticListHead

open NaturalRegisterProgram QuadraticRegisterSystem AnnotatedCodeArithmetic

attribute [local irreducible] Nat.unpair

/-- The upper bound forces output zero at nil; multiplication enforces the
successor marker on every positive code. -/
def GuardCertificate (out code left slack : ℕ) : Prop :=
  (code : ℤ) * ((out : ℤ) - (left : ℤ) - 1) = 0 ∧
  (code : ℤ) - (out : ℤ) - (slack : ℤ) = 0

theorem listHead_le (code : ℕ) : AnnotatedCodeArithmetic.listHead code ≤ code := by
  cases code with
  | zero => simp [AnnotatedCodeArithmetic.listHead]
  | succ code =>
    simp only [AnnotatedCodeArithmetic.listHead,Nat.succ_ne_zero,if_false,Nat.pred_succ]
    exact Nat.succ_le_succ (Nat.unpair_left_le code)

theorem guard_sound {out code left slack : ℕ}
    (h : GuardCertificate out code left slack)
    (hl : left = AnnotatedCodeArithmetic.treeLeft code) :
    out = AnnotatedCodeArithmetic.listHead code := by
  rcases h with ⟨hprod,hbound⟩
  by_cases hc : code = 0
  · subst code
    have ho : out = 0 := by simp only [Nat.cast_zero,zero_sub] at hbound; omega
    simp [ho,AnnotatedCodeArithmetic.listHead]
  · have hci : (code : ℤ) ≠ 0 := by exact_mod_cast hc
    have hd := (mul_eq_zero.mp hprod).resolve_left hci
    have ho : out = left + 1 := by omega
    simp only [AnnotatedCodeArithmetic.listHead,if_neg hc]
    simpa only [hl,AnnotatedCodeArithmetic.treeLeft] using ho

theorem guard_complete (code : ℕ) : GuardCertificate
    (AnnotatedCodeArithmetic.listHead code) code (AnnotatedCodeArithmetic.treeLeft code)
    (code - AnnotatedCodeArithmetic.listHead code) := by
  constructor
  · by_cases hc : code = 0
    · simp [hc]
    · have ho : AnnotatedCodeArithmetic.listHead code =
          AnnotatedCodeArithmetic.treeLeft code + 1 := by
        simp [AnnotatedCodeArithmetic.listHead,AnnotatedCodeArithmetic.treeLeft,hc]
      rw [ho,Nat.cast_add,Nat.cast_one]
      ring
  · have hle := listHead_le code
    have he : code = AnnotatedCodeArithmetic.listHead code +
        (code - AnnotatedCodeArithmetic.listHead code) := by omega
    omega

/-- Slot order: head output, code, left projection, bound slack. -/
def guardProgram : Program 4 := .empty

private def guardInput (i : Fin 4) : Expr (Fin 4 ⊕ Fin guardProgram.nodes.length) :=
  .var (.inl i)

def guardRows : Fin 2 → Expr (Fin 4 ⊕ Fin guardProgram.nodes.length) :=
  ![guardInput 1 * (guardInput 0 - guardInput 2 - 1),
    guardInput 1 - guardInput 0 - guardInput 3]

def guardSystem : System guardProgram :=
  System.ofRows 2 guardRows (by intro i; fin_cases i <;> decide)

theorem guard_holds_iff (x : Fin 4 → ℕ) : guardSystem.Holds x ↔
    GuardCertificate (x 0) (x 1) (x 2) (x 3) := by
  simp [System.Holds,guardSystem,System.ofRows,guardRows,guardInput,Expr.eval,
    natAssignment,GuardCertificate,Fin.forall_fin_succ]

/-- Shared context: output, code, left, predecessor, other component,
pairing selector, pairing slack, maximum, and output-bound slack. -/
def program : Program 9 := .empty

private def projectionPorts : Fin 7 → Slot program :=
  ![.inl 2,.inl 1,.inl 3,.inl 4,.inl 5,.inl 6,.inl 7]
private def guardPorts : Fin 4 → Slot program := ![.inl 0,.inl 1,.inl 2,.inl 8]

def system : System program :=
  (QuadraticTreeCodeGraphs.leftSystem.instantiate program projectionPorts).conjunction
    (guardSystem.instantiate program guardPorts)

theorem holds_iff (x : Fin 9 → ℕ) : system.Holds x ↔
    (x 3 = (x 1).pred ∧ QuadraticNatPairing.Certificate
      (x 3) (x 2) (x 4) (x 5) (x 6) (x 7)) ∧
    GuardCertificate (x 0) (x 1) (x 2) (x 8) := by
  rw [system,System.conjunction_holds,System.instantiate_holds,System.instantiate_holds]
  exact and_congr (QuadraticTreeCodeGraphs.left_holds_iff _) (guard_holds_iff _)

def representation : Rep (Fin 2)
    (fun v => v 0 = AnnotatedCodeArithmetic.listHead (v 1)) :=
  (System.scopedRep (a := 2) (k := 7) system).ofIff (by
    intro v
    simp only [holds_iff]
    change (∃ w : Fin 7 → ℕ, (w 1 = (v 1).pred ∧
      QuadraticNatPairing.Certificate (w 1) (w 0) (w 2) (w 3) (w 4) (w 5)) ∧
      GuardCertificate (v 0) (v 1) (w 0) (w 6)) ↔ _
    constructor
    · rintro ⟨w,⟨hp,hpair⟩,hg⟩
      have hpair' := QuadraticNatPairing.certificate_sound hpair
      have hl : w 0 = AnnotatedCodeArithmetic.treeLeft (v 1) := by
        change w 0 = (Nat.unpair (v 1).pred).1
        rw [←hp,hpair',Nat.unpair_pair]
      exact guard_sound hg hl
    · intro hv
      have hp : (v 1).pred = Nat.pair (Nat.unpair (v 1).pred).1
          (Nat.unpair (v 1).pred).2 := (Nat.pair_unpair _).symm
      obtain ⟨t,s,m,hc⟩ := QuadraticNatPairing.certificate_complete hp
      refine ⟨![(Nat.unpair (v 1).pred).1,(v 1).pred,
        (Nat.unpair (v 1).pred).2,t,s,m,(v 1)-v 0],⟨rfl,hc⟩,?_⟩
      rw [hv]
      exact guard_complete (v 1))

private def graphIndex : Fin 2 → Option (Fin 1) := Fin.cases none (fun _ => some 0)

def listHead : GraphRep (fun v : Fin 1 → ℕ => AnnotatedCodeArithmetic.listHead (v 0)) :=
  (representation.reindex graphIndex).ofIff (fun _ => Iff.rfl)

@[simp] theorem listHead_witnessCount : listHead.witnessCount = 7 := rfl
theorem listHead_binaryOps : listHead.expression.binaryOps = 76 := by decide

theorem listHead_degree : listHead.expression.toPolynomial.totalDegree ≤ 4 := by
  simp only [listHead,Rep.ofIff,Rep.reindex,NaturalRegisterRelation.rename_toPolynomial]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (System.scopedRep_degree (a := 2) (k := 7) system)

end DiophantineConsistency.QuadraticListHead
