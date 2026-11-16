module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalCarryCell
public import M6PA.Model.PAInternalCarryCode
public import M6PA.Model.PAInternalSegmentCompose
@[expose] public section

namespace M6.Arithmetic.PA.InternalTrace.CarryFile
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open CarryCode ScanBits
attribute [local irreducible] Step StepFormula.formula

def carryFormula : ArithmeticSemisentence 1 :=
  “xs. ∀ l t, ∃ r l' c, !rightGraph r xs t ∧ !leftGraph l' xs l ∧ !costGraph c xs ∧
    ∃ qs ls rs, !segmentFormula c qs ls rs 1 l r 1 l' t”
def boundedFormula : ArithmeticSemisentence 1 := “n. ∀ xs < n, !carryFormula xs”

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

lemma carry_correct (xs : V) : (V ⊧/![xs] carryFormula) ↔
    ∀ l t : V, ∃ qs ls rs,
      Segment (cost xs) qs ls rs 1 l (rightFile xs t) 1 (leftFile xs l) t := by
  simp [carryFormula,right_defined.df,left_defined.df,cost_defined.df,segment_correct]

lemma bounded_correct (n : V) : (V ⊧/![n] boundedFormula) ↔
    ∀ xs : V, xs<n → ∀ l t : V, ∃ qs ls rs,
      Segment (cost xs) qs ls rs 1 l (rightFile xs t) 1 (leftFile xs l) t := by
  simp [boundedFormula,carry_correct]

/-- Full PA induction on a bound for the HFS vector code. The tail code is
strictly smaller, permitting arbitrary model-valued vector length and entries. -/
theorem segment (xs l t : V) : ∃ qs ls rs,
    Segment (cost xs) qs ls rs 1 l (rightFile xs t) 1 (leftFile xs l) t := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀ n : V, ∀ xs : V, xs<n → ∀ l t : V, ∃ qs ls rs,
      Segment (cost xs) qs ls rs 1 l (rightFile xs t) 1 (leftFile xs l) t := by
    refine InductionScheme.succ_induction (C := Set.univ)
      (P := fun n : V => ∀ xs : V, xs<n → ∀ l t : V, ∃ qs ls rs,
        Segment (cost xs) qs ls rs 1 l (rightFile xs t) 1 (leftFile xs l) t) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb boundedFormula,by trivial,?_⟩
      intro n
      simpa using (bounded_correct n).symm
    · simp
    · intro n ih xs hxs l t
      by_cases hsmall : xs<n
      · exact ih xs hsmall l t
      have he : xs=n := le_antisymm (lt_succ_iff_le.mp hxs) (le_of_not_gt hsmall)
      subst n
      rcases nil_or_adjoin xs with hz | ⟨p,tail,rfl⟩
      · subst xs
        exact ⟨_,_,_,by simpa using segment_zero (1 : V) l t⟩
      · obtain ⟨cq,cl,cr,hc⟩ := CarryCell.segment p l (rightFile tail t)
        obtain ⟨tq,tl,tr,ht⟩ := ih tail (lt_adjoin' p tail) (repeatBits p 1 (4*l+2)) t
        have joined := segment_compose hc ht
        simpa only [cost_adjoin,right_adjoin,left_adjoin] using joined
  exact all (xs+1) xs (by simp) l t
end Models

def sentence : ArithmeticSentence := “∀ xs, !carryFormula xs”

theorem pa_proves_carry_file : theory ⊢ sentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sentence,models_iff]
  simp [carry_correct]
  exact segment

#print axioms segment
#print axioms pa_proves_carry_file
end M6.Arithmetic.PA.InternalTrace.CarryFile

