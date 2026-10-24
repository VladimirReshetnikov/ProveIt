import DiophantineConsistency.ObjectResidualSquares
import DiophantineConsistency.QuadraticRegisterComposition
import DiophantineConsistency.GatesSemiring

/-! # Literal shared-register quadratic systems on all internal assignments -/
noncomputable section
namespace DiophantineConsistency.ObjectQuadraticSystem
open SetTheory ObjectOmegaSemiring NaturalRegisterProgram QuadraticRegisterSystem
universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

def RowsZero {n : ℕ} {p : Program n} (s : System p)
    (v : Fin n ⊕ Fin p.nodes.length → N H) : Prop := ∀ i,(s.row i).SemiringZero v

theorem conjunction_rows_zero_iff {n : ℕ} {p : Program n} (s t : System p)
    (v : Fin n ⊕ Fin p.nodes.length → N H) :
    RowsZero H (s.conjunction t) v ↔ RowsZero H s v ∧ RowsZero H t v := by
  constructor
  · intro h
    exact ⟨fun i => by simpa only [System.conjunction,Fin.addCases_left] using h (Fin.castAdd t.rowCount i),
      fun i => by simpa only [System.conjunction,Fin.addCases_right] using h (Fin.natAdd s.rowCount i)⟩
  · rintro ⟨hs,ht⟩ i
    refine Fin.addCases (fun j : Fin s.rowCount => ?_) (fun j : Fin t.rowCount => ?_) i
    · simpa only [System.conjunction,Fin.addCases_left] using hs j
    · simpa only [System.conjunction,Fin.addCases_right] using ht j

theorem instantiate_rows_zero_iff {n ports : ℕ} {p : Program n}
    (s : System (Program.empty : Program ports)) (port : Fin ports → Slot p)
    (v : Slot p → N H) :
    RowsZero H (s.instantiate p port) v ↔
      RowsZero H s (Sum.elim (v ∘ port) Fin.elim0) := by
  have he : v ∘ Sum.elim port Fin.elim0=Sum.elim (v ∘ port) Fin.elim0 := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact i.elim0
  simp only [RowsZero,System.instantiate,Expr.semiringZero_rename,he]
  rfl

theorem expression_zero_iff {n : ℕ} {p : Program n} (s : System p)
    (v : Fin n ⊕ Fin p.nodes.length → N H) :
    s.expression.SemiringZero v ↔ ∀ i,(s.residual i).SemiringZero v := by
  have he : s.expression=QuarticSyntax.sumExpressions
      ((List.ofFn s.residual).map (fun e => e*e)) := by
    simp only [System.expression,List.map_ofFn,Function.comp_def]
  rw [he]
  simpa only [List.forall_mem_ofFn_iff,Expr.SemiringZero] using
    ObjectResidualSquares.expression_zero_iff H (List.ofFn s.residual) v

/-- A gate-free local system uses only its supplied rows. -/
theorem empty_expression_zero_iff {n : ℕ}
    (s : System (Program.empty : Program n)) (v : Fin n → N H) :
    s.expression.SemiringZero (Sum.elim v Fin.elim0) ↔
      ∀ i,(s.row i).SemiringZero (Sum.elim v Fin.elim0) := by
  rw [expression_zero_iff]
  constructor <;> intro h i
  · simpa [System.residual,Program.empty,Fin.addCases] using h (Fin.natAdd 0 i)
  · refine Fin.addCases (fun j : Fin 0 => j.elim0) (fun j => ?_) i
    simpa only [System.residual_right] using h j

/-- Remove the empty register block from a gate-free local system. -/
def inputExpression {n : ℕ} (s : System (Program.empty : Program n)) : Expr (Fin n) :=
  s.expression.rename (Sum.elim id Fin.elim0)

theorem inputExpression_degree {n : ℕ} (s : System (Program.empty : Program n)) :
    (inputExpression s).toPolynomial.totalDegree≤4 := by
  rw [inputExpression,QuarticCompiler.Gates.polynomial_rename]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans (System.expression_degree s)

theorem inputExpression_zero_iff {n : ℕ} (s : System (Program.empty : Program n))
    (v : Fin n → N H) : (inputExpression s).SemiringZero v ↔
      RowsZero H s (Sum.elim v Fin.elim0) := by
  rw [inputExpression,Expr.semiringZero_rename]
  have he : v ∘ Sum.elim id Fin.elim0=Sum.elim v Fin.elim0 := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact i.elim0
  rw [he]
  exact empty_expression_zero_iff H s v

end DiophantineConsistency.ObjectQuadraticSystem
