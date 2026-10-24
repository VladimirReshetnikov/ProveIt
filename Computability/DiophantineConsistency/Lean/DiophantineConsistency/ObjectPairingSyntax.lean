import DiophantineConsistency.ObjectNatPairing
import DiophantineConsistency.GatesSemiring

/-! # The literal sharp pairing rows interpreted on the entire internal omega -/
noncomputable section
namespace DiophantineConsistency.ObjectPairingSyntax
open SetTheory
open LeanProofs.BoundedZFCConsistency ObjectOmegaSemiring
private theorem literal_row0 : QuadraticNatPairing.rows 0 2 0 =
    (Expr.mul (.var (.inl (3 : Fin 6)))
    (.sub (.var (.inl 3)) (.constant 1))) := by rfl

private theorem literal_row1 : QuadraticNatPairing.rows 0 2 1 =
    (Expr.sub (.var (.inl (5 : Fin 6)))
    (.add (.mul (.sub (.constant 1) (.var (.inl 3))) (.var (.inl 2)))
      (.mul (.var (.inl 3)) (.var (.inl 0))))) := by rfl

private theorem literal_row2 : QuadraticNatPairing.rows 0 2 2 =
    (Expr.sub (.sub (.add (.var (.inl (2 : Fin 6)))
      (.mul (.var (.inl 3)) (.var (.inl 4)))) (.var (.inl 0)))
    (.mul (.sub (.constant 1) (.var (.inl 3)))
      (.add (.var (.inl 4)) (.constant 1)))) := by rfl

private theorem literal_row3 : QuadraticNatPairing.rows 0 2 3 =
    (Expr.sub (.sub (.sub (.var (.inl (1 : Fin 6)))
    (.mul (.var (.inl 5)) (.var (.inl 5)))) (.var (.inl 0)))
      (.mul (.var (.inl 3)) (.var (.inl 2)))) := by rfl

universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

private def assignment (x : Fin 6 → N H) : Fin 6 ⊕ Fin 0 → N H := Sum.elim x Fin.elim0

private theorem row0 (x : Fin 6 → N H) :
    (QuadraticNatPairing.rows 0 2 0).SemiringZero (assignment H x) ↔ x 3*x 3=x 3 := by
  rw [literal_row0]
  simp [Expr.SemiringZero,Expr.splitNatural,NatExpr.evalSemiring,assignment,Sum.elim]

private theorem row1 (x : Fin 6 → N H) :
    (QuadraticNatPairing.rows 0 2 1).SemiringZero (assignment H x) ↔
      x 5+x 3*x 2=x 2+x 3*x 0 := by
  rw [literal_row1]
  simp [Expr.SemiringZero,Expr.splitNatural,NatExpr.evalSemiring,assignment,Sum.elim]

private theorem row2 (x : Fin 6 → N H) :
    (QuadraticNatPairing.rows 0 2 2).SemiringZero (assignment H x) ↔
      x 2+x 3*x 4+x 3*(x 4+1)=x 0+(x 4+1) := by
  rw [literal_row2]
  simp [Expr.SemiringZero,Expr.splitNatural,NatExpr.evalSemiring,assignment,Sum.elim]

private theorem row3 (x : Fin 6 → N H) :
    (QuadraticNatPairing.rows 0 2 3).SemiringZero (assignment H x) ↔
      x 1=x 5*x 5+x 0+x 3*x 2 := by
  rw [literal_row3]
  simp [Expr.SemiringZero,Expr.splitNatural,NatExpr.evalSemiring,assignment,Sum.elim]

theorem rows_zero_iff (x : Fin 6 → N H) :
    (∀ i, (QuadraticNatPairing.rows 0 2 i).SemiringZero (Sum.elim x Fin.elim0)) ↔
      ObjectNatPairing.Certificate H (x 1) (x 0) (x 2) (x 3) (x 4) (x 5) := by
  constructor
  · intro h
    exact ⟨(row0 H x).mp (h 0),(row1 H x).mp (h 1),(row2 H x).mp (h 2),(row3 H x).mp (h 3)⟩
  · intro h i
    fin_cases i
    · exact (row0 H x).mpr h.1
    · exact (row1 H x).mpr h.2.1
    · exact (row2 H x).mpr h.2.2.1
    · exact (row3 H x).mpr h.2.2.2

/-- The existing sharp quartic, with its empty register block removed. -/
def expression : Expr (Fin 6) :=
  (QuadraticNatPairing.system 0 2).expression.rename (Sum.elim id Fin.elim0)

private theorem literal_residual (i : Fin 4) :
    (QuadraticNatPairing.system 0 2).residual i=QuadraticNatPairing.rows 0 2 i := by
  fin_cases i <;> rfl

private theorem literal_expression : (QuadraticNatPairing.system 0 2).expression=
    QuarticSyntax.sumExpressions ((List.ofFn (QuadraticNatPairing.rows 0 2)).map
      (fun e => e*e)) := by
  simp only [QuadraticRegisterSystem.System.expression,List.map_ofFn]
  congr 1

theorem expression_degree : expression.toPolynomial.totalDegree≤4 := by
  rw [expression,QuarticCompiler.Gates.polynomial_rename]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (QuadraticRegisterSystem.System.expression_degree _)

theorem expression_zero_iff (x : Fin 6 → N H) :
    expression.SemiringZero x ↔
      ObjectNatPairing.Certificate H (x 1) (x 0) (x 2) (x 3) (x 4) (x 5) := by
  rw [expression,Expr.semiringZero_rename,literal_expression]
  have he : x ∘ Sum.elim id Fin.elim0=assignment H x := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact i.elim0
  rw [he]
  have hh := ObjectResidualSquares.expression_zero_iff H
    (List.ofFn (QuadraticNatPairing.rows 0 2)) (assignment H x)
  simp only [List.forall_mem_ofFn_iff] at hh
  exact hh.trans (rows_zero_iff H x)

/-- Three auxiliary internal naturals certify the exact internal pairing,
including nonstandard source values. -/
theorem exists_expression_zero_iff (z a b : N H) :
    (∃ t s m : N H, expression.SemiringZero (![a,z,b,t,s,m] : Fin 6 → N H)) ↔
      z=ObjectNatPairing.pair H a b := by
  simpa [expression_zero_iff] using ObjectNatPairing.exists_certificate_iff H z a b

theorem exists_equationRel_iff (z a b : N H) :
    (∃ t s m : N H, ObjectPolynomial.EquationRel H expression
      (fun i => ((![a,z,b,t,s,m] : Fin 6 → N H) i).val)) ↔
      z=ObjectNatPairing.pair H a b := by
  simpa only [ObjectNaturalSemiring.equationRel_iff,Expr.SemiringZero] using
    exists_expression_zero_iff H z a b

end DiophantineConsistency.ObjectPairingSyntax
