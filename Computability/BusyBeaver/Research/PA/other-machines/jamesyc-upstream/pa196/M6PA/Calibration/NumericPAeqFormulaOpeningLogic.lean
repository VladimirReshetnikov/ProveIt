module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSupportedOpening
public import M6PA.Calibration.FoundationPAeqCodeSubstitutionAgreement
@[expose] public section
namespace M6.PA.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem free_and_code {p q:V} (hp:IsSemiformula language 1 p) (hq:IsSemiformula language 1 q):
    free language (qqAnd p q)=qqAnd (free language p) (free language q) := by
  simp [free,substs1,hp.isUFormula,hq.isUFormula,hp.shift.isUFormula,hq.shift.isUFormula]
theorem free_imp_code {p q:V} (hp:IsSemiformula language 1 p) (hq:IsSemiformula language 1 q):
    free language (imp language p q)=imp language (free language p) (free language q) := by
  simp [free,substs1,Bootstrapping.imp,hp.isUFormula,hq.isUFormula,hp.neg.isUFormula,
    hp.shift.isUFormula,hq.shift.isUFormula,hp.shift.neg.isUFormula,shift_neg hp,
    substs_neg hp.shift (show IsSemitermVec language (1:V) 0 (qqFvar 0∷0) by simp)]
theorem free_zero_arity {p:V} (hp:IsFormula language p):
    free language p=shift language p := by
  unfold free substs1
  rw [FoundationPAeqCode.subst_agree_on_bound hp.shift
    (show IsSemitermVec language (1:V) 0 (qqFvar 0∷0) by simp)
    (show IsSemitermVec language (0:V) 0 0 by simp)
    (by simp) (le_refl 0) (by simp)]
  exact subst_eq_self hp.shift (by simp) (by simp)
theorem free_domain_code :
    free language (⌜NumericPAeqTerm.domainTemplate⌝:V)=NumericPAeqTerm.domainCode (qqFvar 0) := by
  rw [free,NumericPAeqFormula.domainTemplate_code_targetShift]
  rfl
#print axioms free_and_code
#print axioms free_imp_code
#print axioms free_zero_arity
#print axioms free_domain_code
end M6.PA.NumericPAeqFormulaRealization

