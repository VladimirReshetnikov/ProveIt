import DiophantineConsistency.ObjectTreeCodeSyntax
import DiophantineConsistency.QuadraticListHead

/-! # The literal guarded list-head quartic over internal omega -/
noncomputable section
namespace DiophantineConsistency.ObjectListHead
open SetTheory ObjectOmegaSemiring NaturalRegisterProgram QuadraticRegisterSystem

private def projectionPort : Fin 7 → Slot QuadraticListHead.program :=
  ![.inl 2,.inl 1,.inl 3,.inl 4,.inl 5,.inl 6,.inl 7]
private def guardPort : Fin 4 → Slot QuadraticListHead.program := ![.inl 0,.inl 1,.inl 2,.inl 8]
private theorem literal_system : QuadraticListHead.system=
    (QuadraticTreeCodeGraphs.leftSystem.instantiate QuadraticListHead.program projectionPort).conjunction
      (QuadraticListHead.guardSystem.instantiate QuadraticListHead.program guardPort) := rfl
private theorem literal_guard0 : QuadraticListHead.guardRows 0=
    Expr.mul (.var (.inl (1 : Fin 4)))
      (.sub (.sub (.var (.inl 0)) (.var (.inl 2))) (.constant 1)) := rfl
private theorem literal_guard1 : QuadraticListHead.guardRows 1=
    Expr.sub (.sub (.var (.inl (1 : Fin 4))) (.var (.inl 0))) (.var (.inl 3)) := rfl

universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

private theorem self_le_square (x : N H) : x≤x*x := by
  rcases ObjectNaturalDiscrete.zero_or_add_one H x with hz | ⟨s,rfl⟩
  · simp only [hz,zero_mul,le_refl]
  · exact (ObjectNaturalOrder.Natural.le_iff_exists_add H _ _).mpr ⟨(s+1)*s,by ring⟩

theorem left_le_pair (a b : N H) : a≤ObjectNatPairing.pair H a b := by
  have hm : max a b≤ObjectNatPairing.pair H a b :=
    (self_le_square H (max a b)).trans (MaxSquarePairing.max_square_le_pair a b)
  exact le_max_left a b |>.trans hm

theorem listHead_le (code : N H) : ObjectNumericWire.listHead H code≤code := by
  rcases ObjectNumericWire.zero_or_cons H code with hz | hc
  · rw [hz,ObjectNumericWire.head_zero]
  · rw [hc,ObjectNumericWire.head_cons]
    exact add_le_add (left_le_pair H _ _) (le_refl 1)

def GuardCertificate (out code left slack : N H) : Prop :=
  code*out=code*(left+1) ∧ code=out+slack

theorem guard_sound {out code left slack : N H} (h : GuardCertificate H out code left slack)
    (hl : left=ObjectNumericWire.treeLeft H code) : out=ObjectNumericWire.listHead H code := by
  by_cases hz : code=0
  · have ho : out=0 := ((ObjectResidualSquares.add_eq_zero_iff H out slack).mp
      (hz ▸ h.2.symm)).1
    rw [hz,ObjectNumericWire.head_zero,ho]
  · have ho : out=left+1 := mul_left_cancel₀ hz h.1
    simpa only [ObjectNumericWire.listHead,if_neg hz,hl] using ho

theorem guard_complete (code : N H) : ∃ slack,GuardCertificate H
    (ObjectNumericWire.listHead H code) code (ObjectNumericWire.treeLeft H code) slack := by
  obtain ⟨slack,hs⟩ := (ObjectNaturalOrder.Natural.le_iff_exists_add H _ _).mp (listHead_le H code)
  refine ⟨slack,?_,hs.symm⟩
  by_cases hz : code=0
  · simp [hz]
  · simp only [ObjectNumericWire.listHead,if_neg hz]

private theorem guard_rows (x : Fin 4 → N H) :
    ObjectQuadraticSystem.RowsZero H QuadraticListHead.guardSystem (Sum.elim x Fin.elim0) ↔
      GuardCertificate H (x 0) (x 1) (x 2) (x 3) := by
  change (∀ i : Fin 2,(QuadraticListHead.guardRows i).SemiringZero (Sum.elim x Fin.elim0)) ↔ _
  have h0 : (QuadraticListHead.guardRows 0).SemiringZero (Sum.elim x Fin.elim0) ↔
      x 1*x 0=x 1*(x 2+1) := by
    rw [literal_guard0]
    simp [Expr.SemiringZero,Expr.splitNatural,NatExpr.evalSemiring,Sum.elim]
  have h1 : (QuadraticListHead.guardRows 1).SemiringZero (Sum.elim x Fin.elim0) ↔
      x 1=x 0+x 3 := by
    rw [literal_guard1]
    simp [Expr.SemiringZero,Expr.splitNatural,NatExpr.evalSemiring,Sum.elim]
  simp only [Fin.forall_fin_two, h0, h1, GuardCertificate]

theorem rows_zero_iff (x : Fin 9 → N H) :
    ObjectQuadraticSystem.RowsZero H QuadraticListHead.system (Sum.elim x Fin.elim0) ↔
      (x 3=ObjectPredecessor.pred H (x 1) ∧
        ObjectNatPairing.Certificate H (x 3) (x 2) (x 4) (x 5) (x 6) (x 7)) ∧
      GuardCertificate H (x 0) (x 1) (x 2) (x 8) := by
  rw [literal_system,ObjectQuadraticSystem.conjunction_rows_zero_iff,
    ObjectQuadraticSystem.instantiate_rows_zero_iff,ObjectQuadraticSystem.instantiate_rows_zero_iff]
  exact and_congr (ObjectTreeCodeSyntax.left_rows_zero_iff H _) (guard_rows H _)

def expression : Expr (Fin 9) := ObjectQuadraticSystem.inputExpression QuadraticListHead.system
theorem expression_degree : expression.toPolynomial.totalDegree≤4 :=
  ObjectQuadraticSystem.inputExpression_degree _

theorem expression_zero_iff (x : Fin 9 → N H) : expression.SemiringZero x ↔
    (x 3=ObjectPredecessor.pred H (x 1) ∧
      ObjectNatPairing.Certificate H (x 3) (x 2) (x 4) (x 5) (x 6) (x 7)) ∧
    GuardCertificate H (x 0) (x 1) (x 2) (x 8) :=
  (ObjectQuadraticSystem.inputExpression_zero_iff H _ x).trans (rows_zero_iff H x)

theorem exists_expression_zero_iff (out code : N H) :
    (∃ w : Fin 7 → N H,expression.SemiringZero
      (![out,code,w 0,w 1,w 2,w 3,w 4,w 5,w 6] : Fin 9 → N H)) ↔
      out=ObjectNumericWire.listHead H code := by
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨⟨hp,hc⟩,hg⟩ := (expression_zero_iff H _).mp hw
    have he : ObjectPredecessor.pred H code=ObjectNatPairing.pair H (w 0) (w 2) :=
      hp ▸ ObjectNatPairing.certificate_sound H hc
    apply guard_sound H hg
    change w 0=ObjectNumericWire.treeLeft H code
    rw [ObjectNumericWire.treeLeft,he,ObjectUnpair.unpair_pair]
  · intro h
    obtain ⟨w,hw⟩ := (ObjectTreeCodeSyntax.exists_left_zero_iff H
      (ObjectNumericWire.treeLeft H code) code).mpr rfl
    have hp := (ObjectTreeCodeSyntax.left_expression_zero_iff H _).mp hw
    obtain ⟨slack,hg⟩ := guard_complete H code
    exact ⟨![ObjectNumericWire.treeLeft H code,w 0,w 1,w 2,w 3,w 4,slack],
      (expression_zero_iff H _).mpr ⟨hp,h ▸ hg⟩⟩

end DiophantineConsistency.ObjectListHead
