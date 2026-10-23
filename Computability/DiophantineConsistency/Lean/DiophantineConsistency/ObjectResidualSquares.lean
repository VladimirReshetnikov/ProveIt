import DiophantineConsistency.ObjectNaturalOrder
import DiophantineConsistency.ObjectNaturalZero
import DiophantineConsistency.ObjectNaturalSemiring
import DiophantineConsistency.QuarticSyntax

/-! # A sum of residual squares cannot cancel over internal omega

The list of residuals is supplied finite syntax. All of its values range
over the entire internal omega, including nonstandard values.
-/

noncomputable section
namespace DiophantineConsistency.ObjectResidualSquares
open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency ObjectOmegaSemiring

universe u
variable {V : Type u} {mem : V → V → Prop}
abbrev N (H : ZFAxioms mem) := ObjectOmegaSemiring.Natural H

variable (H : ZFAxioms mem)

theorem add_eq_zero_iff (a b : N H) : a+b=0 ↔ a=0 ∧ b=0 := by
  constructor
  · intro h
    have hz := (Natural.addRel_iff H a b 0).mpr h
    obtain ⟨ha,hb⟩ := (ObjectAdditionCancellation.addRel_zero_iff H a.val b.val).mp hz
    exact ⟨Subtype.ext ha,Subtype.ext hb⟩
  · rintro ⟨rfl,rfl⟩
    exact add_zero 0

theorem square_eq_zero_iff (a : N H) : a^2=0 ↔ a=0 := by
  simp only [pow_two,mul_self_eq_zero]

theorem square_gap (a b : N H) : ∃ d : N H,
    a^2+b^2=2*a*b+d^2 ∧ (d=0 ↔ a=b) := by
  have oriented (x y : N H) (hxy : x≤y) : ∃ d : N H,
      x^2+y^2=2*x*y+d^2 ∧ (d=0 ↔ x=y) := by
    obtain ⟨d,hd⟩ := (ObjectNaturalOrder.Natural.le_iff_exists_add H x y).mp hxy
    refine ⟨d,?_,?_⟩
    · rw [← hd]
      ring
    · constructor
      · intro hzero
        simpa only [hzero,add_zero] using hd
      · intro he
        apply add_left_cancel (a := x)
        simpa only [add_zero] using hd.trans he.symm
  rcases le_total a b with hab | hba
  · exact oriented a b hab
  · obtain ⟨d,hd,hzero⟩ := oriented b a hba
    refine ⟨d,?_,hzero.trans eq_comm⟩
    calc
      a^2+b^2=b^2+a^2 := add_comm _ _
      _ = 2*b*a+d^2 := hd
      _ = 2*a*b+d^2 := by ring

def positiveSum : List (N H × N H) → N H
  | [] => 0
  | (a,b)::rows => a^2+b^2+positiveSum rows

def negativeSum : List (N H × N H) → N H
  | [] => 0
  | (a,b)::rows => 2*a*b+negativeSum rows

theorem sum_gap (rows : List (N H × N H)) : ∃ g : N H,
    positiveSum H rows=negativeSum H rows+g ∧
      (g=0 ↔ ∀ p ∈ rows, p.1=p.2) := by
  induction rows with
  | nil => exact ⟨0,by simp [positiveSum,negativeSum],by simp⟩
  | cons p rows ih =>
    obtain ⟨d,hd,hdzero⟩ := square_gap H p.1 p.2
    obtain ⟨g,hg,hgzero⟩ := ih
    refine ⟨d^2+g,?_,?_⟩
    · change p.1^2+p.2^2+positiveSum H rows=(2*p.1*p.2+negativeSum H rows)+(d^2+g)
      rw [hd,hg]
      ring
    · rw [add_eq_zero_iff H,square_eq_zero_iff H,hdzero,hgzero]
      simp only [List.mem_cons,forall_eq_or_imp]

theorem sums_equal_iff (rows : List (N H × N H)) :
    positiveSum H rows=negativeSum H rows ↔ ∀ p ∈ rows,p.1=p.2 := by
  obtain ⟨g,hg,hzero⟩ := sum_gap H rows
  constructor
  · intro h
    apply hzero.mp
    apply add_left_cancel (a := negativeSum H rows)
    rw [← hg,h,add_zero]
  · intro h
    rw [hg,hzero.mpr h,add_zero]

theorem twoSquares_equal_iff (a b : N H) : a^2+b^2=2*a*b ↔ a=b := by
  simpa [positiveSum,negativeSum] using (sums_equal_iff H [(a,b)])

variable {σ : Type*}

def residualPairs (es : List (Expr σ)) (v : σ → N H) : List (N H × N H) :=
  es.map (fun e => (e.splitNatural.1.evalSemiring v,e.splitNatural.2.evalSemiring v))

theorem eval_positive (es : List (Expr σ)) (v : σ → N H) :
    (QuarticSyntax.sumExpressions (es.map (fun e => e*e))).splitNatural.1.evalSemiring v=
      positiveSum H (residualPairs H es v) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change (e.splitNatural.1.evalSemiring v*e.splitNatural.1.evalSemiring v+
      e.splitNatural.2.evalSemiring v*e.splitNatural.2.evalSemiring v)+
        (QuarticSyntax.sumExpressions (es.map (fun e => e*e))).splitNatural.1.evalSemiring v =
          (e.splitNatural.1.evalSemiring v^2+e.splitNatural.2.evalSemiring v^2)+
            positiveSum H (residualPairs H es v)
    rw [ih]
    simp only [pow_two]

theorem eval_negative (es : List (Expr σ)) (v : σ → N H) :
    (QuarticSyntax.sumExpressions (es.map (fun e => e*e))).splitNatural.2.evalSemiring v=
      negativeSum H (residualPairs H es v) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change (e.splitNatural.1.evalSemiring v*e.splitNatural.2.evalSemiring v+
      e.splitNatural.2.evalSemiring v*e.splitNatural.1.evalSemiring v)+
        (QuarticSyntax.sumExpressions (es.map (fun e => e*e))).splitNatural.2.evalSemiring v =
          2*e.splitNatural.1.evalSemiring v*e.splitNatural.2.evalSemiring v+
            negativeSum H (residualPairs H es v)
    rw [ih]
    ring

/-- Exact conjunction semantics for the actual residual-square expression. -/
theorem expression_zero_iff (es : List (Expr σ)) (v : σ → N H) :
    (QuarticSyntax.sumExpressions (es.map (fun e => e*e))).splitNatural.1.evalSemiring v=
      (QuarticSyntax.sumExpressions (es.map (fun e => e*e))).splitNatural.2.evalSemiring v ↔
        ∀ e ∈ es,e.splitNatural.1.evalSemiring v=e.splitNatural.2.evalSemiring v := by
  rw [eval_positive,eval_negative,sums_equal_iff]
  simp only [residualPairs,List.forall_mem_map]

theorem equationRel_iff {n : ℕ} (es : List (Expr (Fin n))) (v : Fin n → N H) :
    ObjectPolynomial.EquationRel H (QuarticSyntax.sumExpressions (es.map (fun e => e*e)))
      (fun i => (v i).val) ↔
        ∀ e ∈ es,ObjectPolynomial.EquationRel H e (fun i => (v i).val) := by
  rw [ObjectNaturalSemiring.equationRel_iff,expression_zero_iff]
  exact forall_congr' (fun e => imp_congr_right (fun _ =>
    (ObjectNaturalSemiring.equationRel_iff H e v).symm))

def conjunctionForm {n : ℕ} : List (Expr (Fin n)) → Form
  | [] => fEq 0 0
  | e::es => fAnd (ObjectPolynomial.equationForm e Fin.val) (conjunctionForm es)

theorem conjunctionForm_spec {n : ℕ} (es : List (Expr (Fin n))) (ee : Nat → V) :
    Sat mem ee (conjunctionForm es) ↔
      ∀ e ∈ es,ObjectPolynomial.EquationRel H e (ee ∘ Fin.val) := by
  induction es with
  | nil =>
    change (ee 0=ee 0) ↔ _
    simp
  | cons e es ih =>
    change (Sat mem ee (ObjectPolynomial.equationForm e Fin.val) ∧
      Sat mem ee (conjunctionForm es)) ↔ _
    rw [ObjectPolynomial.equationForm_spec H,ih]
    simp only [List.mem_cons,forall_eq_or_imp]

def residualConjunctionSentence {n : ℕ} (es : List (Expr (Fin n))) : Form := sealF
  (fImp (ObjectNaturalExpression.inputsNaturalForm (Fin.val : Fin n → Nat))
    (fIff (ObjectPolynomial.equationForm
      (QuarticSyntax.sumExpressions (es.map (fun e => e*e))) Fin.val) (conjunctionForm es)))

theorem sentence_residualConjunctionSentence {n : ℕ} (es : List (Expr (Fin n))) :
    Sentence (residualConjunctionSentence es) := Sentence_seal _

/-- The sum-of-squares step itself is proved in the actual sealed ZFC calculus. -/
theorem zfc_proves_residual_conjunction {n : ℕ} (es : List (Expr (Fin n))) :
    BProv ZFCax_s [] (residualConjunctionSentence es) := by
  apply completeness_inf_context ZFCax_s [] _ Sentences_ZFC
  intro Dom m ee hmodel _
  let H := ObjectMultiplication.axioms_of_zfc_model ee hmodel
  apply (seal_valid (mem := m) _).mpr ?_ ee
  intro env hnat
  have hv := (ObjectNaturalExpression.inputsNaturalForm_spec H _ env).mp hnat
  let v : Fin n → N H := fun i => ⟨env i.val,hv i⟩
  have hiff := (ObjectPolynomial.equationForm_spec H
    (QuarticSyntax.sumExpressions (es.map (fun e => e*e))) Fin.val env).trans
      ((equationRel_iff H es v).trans (conjunctionForm_spec H es env).symm)
  exact ⟨hiff.mp,hiff.mpr⟩

end DiophantineConsistency.ObjectResidualSquares
