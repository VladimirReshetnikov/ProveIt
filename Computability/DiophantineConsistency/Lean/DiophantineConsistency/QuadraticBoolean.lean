import DiophantineConsistency.QuadraticRegisterComposition

/-! # Quadratic zero tests and conditional selection on shared natural slots -/

namespace DiophantineConsistency.QuadraticBoolean

open NaturalRegisterProgram QuadraticRegisterSystem

/-- The bit is one exactly at zero. The slack witnesses strict positivity
in the other branch, including when the tested number is one. -/
def ZeroCertificate (bit n slack : ℕ) : Prop :=
  (bit : ℤ) * ((bit : ℤ) - 1) = 0 ∧
  (bit : ℤ) * (n : ℤ) = 0 ∧
  (n : ℤ) - (1 - (bit : ℤ)) * ((slack : ℤ) + 1) = 0

theorem zero_certificate_sound {bit n slack : ℕ} (h : ZeroCertificate bit n slack) :
    bit = if n = 0 then 1 else 0 := by
  rcases h with ⟨hb,hn,hs⟩
  rcases mul_eq_zero.mp hb with hb | hb
  · have hb0 : bit = 0 := by exact_mod_cast hb
    subst bit
    have hn0 : n ≠ 0 := by simp only [Nat.cast_zero,sub_zero,one_mul] at hs; omega
    simp [hn0]
  · have hb1 : bit = 1 := by omega
    subst bit
    have hn0 : n = 0 := by simpa using hn
    simp [hn0]

theorem zero_certificate_complete (n : ℕ) :
    ZeroCertificate (if n = 0 then 1 else 0) n n.pred := by
  cases n with
  | zero => simp [ZeroCertificate]
  | succ n => simp [ZeroCertificate,Nat.cast_add]

theorem exists_zero_certificate_iff (bit n : ℕ) :
    (∃ slack, ZeroCertificate bit n slack) ↔ bit = if n = 0 then 1 else 0 := by
  constructor
  · rintro ⟨s,hs⟩; exact zero_certificate_sound hs
  · intro h; subst bit; exact ⟨n.pred,zero_certificate_complete n⟩

/-- Slot order: output bit, tested number, positivity slack. -/
def zeroProgram : Program 3 := .empty

private def zeroInput (i : Fin 3) : Expr (Fin 3 ⊕ Fin zeroProgram.nodes.length) :=
  .var (.inl i)

def zeroRows : Fin 3 → Expr (Fin 3 ⊕ Fin zeroProgram.nodes.length) :=
  ![zeroInput 0 * (zeroInput 0 - 1),
    zeroInput 0 * zeroInput 1,
    zeroInput 1 - (1 - zeroInput 0) * (zeroInput 2 + 1)]

def zeroSystem : System zeroProgram :=
  System.ofRows 3 zeroRows (by intro i; fin_cases i <;> decide)

theorem zero_holds_iff (x : Fin 3 → ℕ) :
    zeroSystem.Holds x ↔ ZeroCertificate (x 0) (x 1) (x 2) := by
  simp [System.Holds,zeroSystem,System.ofRows,zeroRows,zeroInput,Expr.eval,
    natAssignment,ZeroCertificate,Fin.forall_fin_succ]

def zeroRepresentation : Rep (Fin 2) (fun v => v 0 = if v 1 = 0 then 1 else 0) :=
  (System.scopedRep (a := 2) (k := 1) zeroSystem).ofIff (by
    intro v
    simp only [zero_holds_iff]
    change (∃ w : Fin 1 → ℕ, ZeroCertificate (v 0) (v 1) (w 0)) ↔ _
    constructor
    · rintro ⟨w,hw⟩; exact zero_certificate_sound hw
    · intro h; rw [h]; exact ⟨fun _ => (v 1).pred,zero_certificate_complete (v 1)⟩)

private def unaryGraphIndex : Fin 2 → Option (Fin 1) := Fin.cases none (fun _ => some 0)

def zeroTest : GraphRep (fun v : Fin 1 → ℕ => if v 0 = 0 then 1 else 0) :=
  (zeroRepresentation.reindex unaryGraphIndex).ofIff (fun _ => Iff.rfl)

/-- Inputs: output, tested number, zero branch, positive branch, bit, slack. -/
def conditionalProgram : Program 6 := .empty

private def conditionalInput (i : Fin 6) : Expr (Fin 6 ⊕ Fin conditionalProgram.nodes.length) :=
  .var (.inl i)

private def zeroPorts : Fin 3 → Slot conditionalProgram := ![.inl 4,.inl 1,.inl 5]

def selectionSystem : System conditionalProgram := System.ofRows 1
  (fun _ => conditionalInput 0 - (conditionalInput 4 * conditionalInput 2 +
    (1 - conditionalInput 4) * conditionalInput 3)) (by intro i; decide)

def conditionalSystem : System conditionalProgram :=
  (zeroSystem.instantiate conditionalProgram zeroPorts).conjunction selectionSystem

theorem conditional_holds_iff (x : Fin 6 → ℕ) : conditionalSystem.Holds x ↔
    ZeroCertificate (x 4) (x 1) (x 5) ∧
    (x 0 : ℤ) - ((x 4 : ℤ) * (x 2 : ℤ) + (1 - (x 4 : ℤ)) * (x 3 : ℤ)) = 0 := by
  rw [conditionalSystem,System.conjunction_holds,System.instantiate_holds]
  apply and_congr (zero_holds_iff _)
  simp [System.Holds,selectionSystem,System.ofRows,conditionalInput,Expr.eval,natAssignment]

def conditionalRepresentation : Rep (Fin 4)
    (fun v => v 0 = if v 1 = 0 then v 2 else v 3) :=
  (System.scopedRep (a := 4) (k := 2) conditionalSystem).ofIff (by
    intro v
    simp only [conditional_holds_iff]
    change (∃ w : Fin 2 → ℕ, ZeroCertificate (w 0) (v 1) (w 1) ∧
      (v 0 : ℤ) - ((w 0 : ℤ) * (v 2 : ℤ) + (1 - (w 0 : ℤ)) * (v 3 : ℤ)) = 0) ↔ _
    constructor
    · rintro ⟨w,hw,he⟩
      have hb := zero_certificate_sound hw
      by_cases hn : v 1 = 0
      · have hb1 : w 0 = 1 := by simpa [hn] using hb
        simpa [hn,hb1,sub_eq_zero] using he
      · have hb0 : w 0 = 0 := by simpa [hn] using hb
        simpa [hn,hb0,sub_eq_zero] using he
    · intro h
      refine ⟨![if v 1 = 0 then 1 else 0,(v 1).pred],zero_certificate_complete (v 1),?_⟩
      by_cases hn : v 1 = 0 <;> simp [hn] at h ⊢ <;> rw [h] <;> ring)

private def conditionalGraphIndex : Fin 4 → Option (Fin 3) :=
  Fin.cases none some

def ifZero : GraphRep (fun v : Fin 3 → ℕ => if v 0 = 0 then v 1 else v 2) :=
  (conditionalRepresentation.reindex conditionalGraphIndex).ofIff (fun _ => Iff.rfl)

@[simp] theorem zeroTest_witnessCount : zeroTest.witnessCount = 1 := rfl
@[simp] theorem ifZero_witnessCount : ifZero.witnessCount = 2 := rfl
theorem zeroTest_binaryOps : zeroTest.expression.binaryOps = 20 := by decide
theorem ifZero_binaryOps : ifZero.expression.binaryOps = 32 := by decide

theorem zeroTest_degree : zeroTest.expression.toPolynomial.totalDegree ≤ 4 := by
  simp only [zeroTest,Rep.ofIff,Rep.reindex,NaturalRegisterRelation.rename_toPolynomial]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (System.scopedRep_degree (a := 2) (k := 1) zeroSystem)

theorem ifZero_degree : ifZero.expression.toPolynomial.totalDegree ≤ 4 := by
  simp only [ifZero,Rep.ofIff,Rep.reindex,NaturalRegisterRelation.rename_toPolynomial]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (System.scopedRep_degree (a := 4) (k := 2) conditionalSystem)

end DiophantineConsistency.QuadraticBoolean
