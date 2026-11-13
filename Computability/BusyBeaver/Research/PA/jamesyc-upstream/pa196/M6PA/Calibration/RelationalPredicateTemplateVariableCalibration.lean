module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateVariableProof
public import M6PA.Calibration.RelationalPredicateTemplateClosedCalibration
public import M6PA.Calibration.RelationalPredicateTemplateLiftSyntax
public import M6PA.Calibration.RelationalPredicateTemplateSourceInstance
public import M6PA.Calibration.NumericPAeqTermConstructors
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate.Variable
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

def body : RelationalSource.Ordinal.Formula 1 :=
  RelationalSource.Ordinal.domain (.bvar 0) 🡒
    ∃¹ (RelationalSource.Ordinal.domain (.bvar 0) ⋏ RelationalSource.ND.eq (.bvar 0) (.bvar 1))
noncomputable def variableTotalityCode (x : V) : V := templateOne body x

theorem body_closed : body.freeVariables=∅ := by decide

theorem body_instance : (liftFormula body)/[(.fvar 0 : Term 0)]=statement := by
  simp only [body,lift_imp,lift_exs,lift_and,lift_domain,lift_eq,liftTerm,Semiterm.lMap]
  variableTemplateSyntax

theorem statement_value {P f : V} (hP : IsSemiformula L 1 P)
    (hf : IsSemitermVec L (len f) 0 f) (h0 : (0:V)<len f) :
    formulaValue statement P 0 f=variableTotalityCode (nth f 0) := by
  have hs : ∀i,(liftFormula body).FVar? i→(i:V)<len f := by
    intro i hi; simp [Semiformula.FVar?,liftFormula,body_closed] at hi
  have ht : ∀i,(.fvar 0 : Term 0).FVar? i→(i:V)<len f := by
    intro i hi; have hi' : 0=i := by simpa using hi
    subst i; simpa using h0
  have he := formulaValue_instance_alignment (liftFormula body) (.fvar 0) hP hf hs ht
  have hv : EnvironmentsValid (1:V) 1 (qqBvar 0∷0) (bindFree f) :=
    ⟨by simp,by simpa [bindFree,shiftTerms_length hf] using shiftTerms_isSemitermVec hf⟩
  have hb : IdentityBound 1 (qqBvar (0:V)∷(0:V)) := by intro i; fin_cases i; simp
  rw [closed_formulaValue_lift body (by simpa using hv) hb (by
    intro i hi; simp [Semiformula.FVar?,body_closed] at hi),body_instance] at he
  exact he.symm

#print axioms body_instance
#print axioms statement_value
end M6.PA.RelationalPredicateTemplate.Variable
