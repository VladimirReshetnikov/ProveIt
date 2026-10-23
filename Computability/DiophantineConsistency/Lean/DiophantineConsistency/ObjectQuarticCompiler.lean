import DiophantineConsistency.QuarticSemiring
import DiophantineConsistency.ObjectResidualSquares

/-! # The literal tree-to-quartic conversion proved in the sealed ZFC calculus

The source and target are supplied finite arithmetic syntax. The equivalence
covers every model's entire omega. It does not transfer an arbitrary external
representation theorem or establish the consistency calibration.
-/

noncomputable section
namespace DiophantineConsistency.ObjectQuarticCompiler
open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency ObjectOmegaSemiring QuarticCompiler

universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

theorem expression_zero_iff {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m))
    (a : Fin (witnessCount p q+1) → N H) :
    (QuarticSyntax.expression p q).SemiringZero a ↔
      ∀ i, (residualSyntax p q i).SemiringZero (a ∘ coordinate p q) := by
  rw [QuarticSyntax.expression,Expr.semiringZero_rename]
  have hh := ObjectResidualSquares.expression_zero_iff H
    (List.ofFn (fun i => residualSyntax p q ((QuarticSyntax.equationIndex p q).symm i)))
    (a ∘ coordinate p q)
  change _ ↔ ∀ i, (residualSyntax p q i).SemiringZero (a ∘ coordinate p q)
  simp only [List.map_ofFn,List.forall_mem_ofFn_iff] at hh
  apply hh.trans
  constructor
  · intro h i
    simpa only [Equiv.symm_apply_apply,Expr.SemiringZero] using h (QuarticSyntax.equationIndex p q i)
  · intro h i
    exact h _

theorem exists_expression_zero_iff {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    (∃ a : Fin (witnessCount p q+1) → N H, (QuarticSyntax.expression p q).SemiringZero a) ↔
      ∃ v : Fin m → N H, p.evalSemiring (Sum.elim Empty.elim v)=
        q.evalSemiring (Sum.elim Empty.elim v) := by
  constructor
  · rintro ⟨a,ha⟩
    have he : a ∘ coordinate p q=semiringAssignment (a (coordinate p q none))
        (fun i => a (coordinate p q (some i))) := by
      funext i
      cases i <;> rfl
    have hh := (expression_zero_iff H p q a).mp ha
    rw [he] at hh
    exact (exists_residuals_iff p q _).mp ⟨_,hh⟩
  · rintro ⟨v,hv⟩
    obtain ⟨w,hw⟩ := (exists_residuals_iff p q (0 : N H)).mpr ⟨v,hv⟩
    let a := semiringAssignment (0 : N H) w ∘ (coordinate p q).symm
    refine ⟨a,(expression_zero_iff H p q a).mpr ?_⟩
    have he : a ∘ coordinate p q=semiringAssignment (0 : N H) w := by
      funext i
      simp only [Function.comp_apply,a,Equiv.symm_apply_apply]
    rw [he]
    exact hw

/-- Apply the existing literal quartic syntax to the supplied source residual. -/
def compiledExpression {m : ℕ} (e : Expr (Fin m)) :
    Expr (Fin (witnessCount (e.rename Sum.inr).splitNatural.1
      (e.rename Sum.inr).splitNatural.2+1)) :=
  QuarticSyntax.expression (e.rename Sum.inr).splitNatural.1 (e.rename Sum.inr).splitNatural.2

theorem compiled_degree_le_four {m : ℕ} (e : Expr (Fin m)) :
    (compiledExpression e).toPolynomial.totalDegree ≤ 4 := by
  rw [compiledExpression,QuarticSyntax.polynomial_expression]
  exact quartic_degree _ _

theorem exists_compiled_zero_iff {m : ℕ} (e : Expr (Fin m)) :
    (∃ a : _, (compiledExpression e).SemiringZero (a : _ → N H)) ↔
      ∃ v : Fin m → N H, e.SemiringZero v := by
  rw [compiledExpression,exists_expression_zero_iff]
  apply exists_congr
  intro v
  exact Expr.semiringZero_rename e Sum.inr (Sum.elim Empty.elim v)

theorem noZeroRel_compiled_iff {m : ℕ} (e : Expr (Fin m)) :
    ObjectPolynomial.NoZeroRel H (compiledExpression e) ↔ ObjectPolynomial.NoZeroRel H e := by
  rw [ObjectNaturalSemiring.noZeroRel_iff,ObjectNaturalSemiring.noZeroRel_iff]
  simpa only [Expr.SemiringZero,not_exists] using not_congr (exists_compiled_zero_iff H e)

/-- A concrete closed sentence comparing the actual polynomial-side formulas. -/
def compilerSentence {m : ℕ} (e : Expr (Fin m)) : Form :=
  fIff (ObjectPolynomial.noZeroForm (compiledExpression e)) (ObjectPolynomial.noZeroForm e)

theorem sentence_compilerSentence {m : ℕ} (e : Expr (Fin m)) : Sentence (compilerSentence e) := by
  intro i hi
  have ha := ObjectPolynomial.sentence_noZeroForm (compiledExpression e) i
  have hb := ObjectPolynomial.sentence_noZeroForm e i
  change (Free i (ObjectPolynomial.noZeroForm (compiledExpression e)) ∨
    Free i (ObjectPolynomial.noZeroForm e)) ∨
    (Free i (ObjectPolynomial.noZeroForm e) ∨
      Free i (ObjectPolynomial.noZeroForm (compiledExpression e))) at hi
  exact hi.elim (fun h => h.elim ha hb) (fun h => h.elim hb ha)

/-- ZFC itself proves the literal quartic conversion, with no consistency premise. -/
theorem zfc_proves_compiler {m : ℕ} (e : Expr (Fin m)) :
    BProv ZFCax_s [] (compilerSentence e) := by
  apply completeness_inf_context ZFCax_s [] _ Sentences_ZFC
  intro Dom relation env hmodel _
  let HH := ObjectMultiplication.axioms_of_zfc_model env hmodel
  have closed (f : Expr (Fin m)) :
      Sat relation env (ObjectPolynomial.noZeroForm f) ↔ ObjectPolynomial.NoZeroRel HH f := by
    rw [← ObjectPolynomial.sat_noZeroForm_iff HH]
    exact ⟨fun h ee => (Sat_sentence_inv _ (ObjectPolynomial.sentence_noZeroForm f) env ee).mp h,
      fun h => h env⟩
  have closedTarget : Sat relation env (ObjectPolynomial.noZeroForm (compiledExpression e)) ↔
      ObjectPolynomial.NoZeroRel HH (compiledExpression e) := by
    rw [← ObjectPolynomial.sat_noZeroForm_iff HH]
    exact ⟨fun h ee => (Sat_sentence_inv _ (ObjectPolynomial.sentence_noZeroForm _) env ee).mp h,
      fun h => h env⟩
  have hi := closedTarget.trans ((noZeroRel_compiled_iff HH e).trans (closed e).symm)
  exact ⟨hi.mp,hi.mpr⟩

end DiophantineConsistency.ObjectQuarticCompiler
