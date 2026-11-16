module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSubstitutionTerms
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
/-- Bound substitution changes the argument of the unary hole, not its free parameters. -/
theorem atomValue_subst {s k : Nat} (r : Relation k) (ts : Fin k → Term s)
    {n m P b f w : V} (hP : IsSemiformula L 1 P)
    (h : EnvironmentsValid (s:V) n b f) (hw : IsSemitermVec L n m w)
    (hf : ∀j i,(ts j).FVar? i→(i:V)<len f) :
    subst L w (atomValue r ts P b f)=atomValue r ts P (substTerms w b) (substTerms w f) := by
  have ht j := termValue_isSemiterm (ts j) h (hf j)
  cases r with
  | eq =>
    simp only [atomValue]
    rw [substs_rel (by simp) (by simp [(ht 0).isUTerm,(ht 1).isUTerm]),
      termSubstVec_cons₂ (ht 0).isUTerm (ht 1).isUTerm,
      termValue_subst (ts 0) h (hf 0),termValue_subst (ts 1) h (hf 1)]
  | mem =>
    simp only [atomValue]
    rw [substs_rel (by simp) (by simp [(ht 0).isUTerm,(ht 1).isUTerm]),
      termSubstVec_cons₂ (ht 0).isUTerm (ht 1).isUTerm,
      termValue_subst (ts 0) h (hf 0),termValue_subst (ts 1) h (hf 1)]
  | predicate =>
    simp only [atomValue,substs1]
    rw [substs_substs hP hw (by simp [ht 0]),termSubstVec_cons₁ (ht 0).isUTerm,
      termValue_subst (ts 0) h (hf 0)]
#print axioms atomValue_subst
end M6.PA.RelationalPredicateTemplate

