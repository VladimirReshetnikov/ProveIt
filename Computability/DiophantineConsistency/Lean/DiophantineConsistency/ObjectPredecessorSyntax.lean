import DiophantineConsistency.ObjectPredecessor
import DiophantineConsistency.ObjectQuadraticSystem
import DiophantineConsistency.QuadraticTreeCodeGraphs

/-! # The literal checker predecessor quartic over internal omega -/
noncomputable section
namespace DiophantineConsistency.ObjectPredecessorSyntax
set_option maxRecDepth 16000
open SetTheory SetTheory.Form ObjectOmegaSemiring
open LeanProofs.BoundedZFCConsistency

private theorem literal_row0 : QuadraticTreeCodeGraphs.predRows 0=
    Expr.mul (.var (.inl (1 : Fin 2)))
      (.sub (.add (.var (.inl 0)) (.constant 1)) (.var (.inl 1))) := rfl
private theorem literal_row1 : QuadraticTreeCodeGraphs.predRows 1=
    Expr.mul (.var (.inl (0 : Fin 2)))
      (.sub (.add (.var (.inl 0)) (.constant 1)) (.var (.inl 1))) := rfl

universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

theorem rows_zero_iff (x : Fin 2 → N H) :
    (∀ i,(QuadraticTreeCodeGraphs.predRows i).SemiringZero (Sum.elim x Fin.elim0)) ↔
      ObjectPredecessor.Certificate H (x 0) (x 1) := by
  have h0 : (QuadraticTreeCodeGraphs.predRows 0).SemiringZero (Sum.elim x Fin.elim0) ↔
      x 1*(x 0+1)=x 1*x 1 := by
    rw [literal_row0]
    simp [Expr.SemiringZero,Expr.splitNatural,NatExpr.evalSemiring,Sum.elim]
  have h1 : (QuadraticTreeCodeGraphs.predRows 1).SemiringZero (Sum.elim x Fin.elim0) ↔
      x 0*(x 0+1)=x 0*x 1 := by
    rw [literal_row1]
    simp [Expr.SemiringZero,Expr.splitNatural,NatExpr.evalSemiring,Sum.elim]
  constructor
  · intro h
    exact ⟨h0.mp (h 0),h1.mp (h 1)⟩
  · intro h i
    fin_cases i
    · exact h0.mpr h.1
    · exact h1.mpr h.2

def expression : Expr (Fin 2) :=
  QuadraticTreeCodeGraphs.predSystem.expression.rename (Sum.elim id Fin.elim0)

theorem expression_degree : expression.toPolynomial.totalDegree≤4 := by
  rw [expression,QuarticCompiler.Gates.polynomial_rename]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (QuadraticRegisterSystem.System.expression_degree _)

theorem expression_zero_iff (x : Fin 2 → N H) :
    expression.SemiringZero x ↔ x 0=ObjectPredecessor.pred H (x 1) := by
  rw [expression,Expr.semiringZero_rename]
  have he : x ∘ Sum.elim id Fin.elim0=Sum.elim x Fin.elim0 := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact i.elim0
  rw [he]
  exact (ObjectQuadraticSystem.empty_expression_zero_iff H
    QuadraticTreeCodeGraphs.predSystem x).trans
      ((rows_zero_iff H x).trans (ObjectPredecessor.certificate_iff H (x 0) (x 1)))

attribute [local irreducible] expression

/-- No auxiliary coordinate is needed for the predecessor graph. -/
def graphForm (out n : ℕ) : Form :=
  fAnd (fNatF out) (fAnd (fNatF n)
    (ObjectPolynomial.equationForm expression ![out,n]))

theorem graphForm_spec (ee : ℕ → V) (out n : ℕ)
    (ho : mem (ee out) (omegaV H)) (hn : mem (ee n) (omegaV H)) :
    Sat mem ee (graphForm out n) ↔
      (⟨ee out,ho⟩ : N H)=ObjectPredecessor.pred H ⟨ee n,hn⟩ := by
  have he : ObjectPolynomial.EquationRel H expression (ee ∘ (![out,n] : Fin 2 → ℕ)) ↔
      (⟨ee out,ho⟩ : N H)=ObjectPredecessor.pred H ⟨ee n,hn⟩ := by
    have hh := ObjectNaturalSemiring.equationRel_iff H expression
      (![⟨ee out,ho⟩,⟨ee n,hn⟩] : Fin 2 → N H)
    have hv : (fun i => ((![⟨ee out,ho⟩,⟨ee n,hn⟩] : Fin 2 → N H) i).val)=
        ee ∘ (![out,n] : Fin 2 → ℕ) := by
      funext i
      fin_cases i <;> rfl
    rw [hv] at hh
    exact hh.trans (expression_zero_iff H _)
  exact ⟨fun h => he.mp ((ObjectPolynomial.equationForm_spec H expression _ ee).mp h.2.2),
    fun h => ⟨(fNatF_spec H ee out).mpr ho,(fNatF_spec H ee n).mpr hn,
      (ObjectPolynomial.equationForm_spec H expression _ ee).mpr (he.mpr h)⟩⟩

def totalForm : Form := sealF (fImp (fNatF 0) (fEx (graphForm 0 1)))
theorem sentence_totalForm : Sentence totalForm := Sentence_seal _

theorem zfc_proves_total : BProv ZFCax_s [] totalForm := by
  refine completeness_inf_context ZFCax_s [] totalForm Sentences_ZFC ?_
  intro Dom relation env hmodel _
  let HH := ObjectMultiplication.axioms_of_zfc_model env hmodel
  apply (seal_valid (mem := relation) _).mpr ?_ env
  intro ee h
  have hn := (fNatF_spec HH ee 0).mp h
  let out := ObjectPredecessor.pred HH ⟨ee 0,hn⟩
  exact ⟨out.val,(graphForm_spec HH _ 0 1 out.property hn).mpr rfl⟩

end DiophantineConsistency.ObjectPredecessorSyntax
