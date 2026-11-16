module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaValidity
public import M6PA.Calibration.NumericPAeqTermTargetSubstTemplates
public import M6PA.Calibration.NumericPAeqValueIsoCode
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem domainTemplate_targetSubst {n m w : V} (hw : IsSemitermVec language n m w) :
    subst language (qVec language w) (⌜NumericPAeqTerm.domainTemplate⌝ : V)=⌜NumericPAeqTerm.domainTemplate⌝ := by
  have hd := NumericPAeqTerm.domainCode_quote (V:=V) (.bvar 0 : RelationalSource.Ordinal.Term 1)
  change NumericPAeqTerm.domainCode (qqBvar 0)= (⌜NumericPAeqTerm.domainTemplate⌝ : V) at hd
  rw [←hd,NumericPAeqTerm.domainCode_targetSubst hw.qVec (show IsSemiterm language (n+1) (qqBvar 0) by simp)]
  simp [qVec]

theorem equalityTail_targetSubst {n m w : V} (hw : IsSemitermVec language n m w) :
    subst language (qVec language (qVec language w)) (⌜equalityTail⌝ : V)=⌜equalityTail⌝ := by
  have he := NumericPAeqValueIsoGuard.isoCode_quote (V:=V) (.bvar 1 : RelationalSource.Ordinal.Term 2) (.bvar 0)
  have he : NumericPAeqTerm.templateTwo NumericPAeqValueIsoGuard.isoTemplate (qqBvar 1) (qqBvar 0)= (⌜equalityTail⌝ : V) := by
    simpa [NumericPAeqValueIsoGuard.isoCode,equalityTail] using he
  rw [←he,NumericPAeqTerm.templateTwo_targetSubst _ hw.qVec.qVec
    (show IsSemiterm language ((n+1)+1) (qqBvar 1) by simp)
    (show IsSemiterm language ((n+1)+1) (qqBvar 0) by simp)]
  have h1 : termSubst language (qVec language (qVec language w)) (qqBvar (1:V))=qqBvar 1 := by
    simpa [qVec] using substs_qVec_bShift (show IsSemiterm language (n+1) (qqBvar (0:V)) by simp) hw.qVec
  rw [h1]
  simp [qVec]

theorem equalityCode_targetSubst {n m w a b : V} (hw : IsSemitermVec language n m w)
    (ha : IsSemiformula language ((n+1)+1) a) (hb : IsSemiformula language ((n+1)+1) b) :
    subst language w (equalityCode a b)=equalityCode
      (subst language (qVec language (qVec language w)) a) (subst language (qVec language (qVec language w)) b) := by
  have ht : IsUFormula language (⌜equalityTail⌝ : V) := (Semiformula.quote_isSemiformula equalityTail).isUFormula
  simp [equalityCode,ha.isUFormula,hb.isUFormula,ht,equalityTail_targetSubst hw]

theorem guardedAllCode_targetSubst {n m w p : V} (hw : IsSemitermVec language n m w)
    (hp : IsSemiformula language (n+1) p) :
    subst language w (guardedAllCode p)=guardedAllCode (subst language (qVec language w) p) := by
  have hd : IsSemiformula language (n+1) (⌜NumericPAeqTerm.domainTemplate⌝ : V) := by
    have h := Semiformula.quote_isSemiformula (V:=V) NumericPAeqTerm.domainTemplate
    exact ⟨h.isUFormula,le_trans h.bv_le (by simp)⟩
  simp [guardedAllCode,Bootstrapping.imp,hd.isUFormula,hp.isUFormula,
    substs_neg hd hw.qVec,domainTemplate_targetSubst hw]

theorem guardedExsCode_targetSubst {n m w p : V} (hw : IsSemitermVec language n m w)
    (hp : IsSemiformula language (n+1) p) :
    subst language w (guardedExsCode p)=guardedExsCode (subst language (qVec language w) p) := by
  have hd : IsUFormula language (⌜NumericPAeqTerm.domainTemplate⌝ : V) := (Semiformula.quote_isSemiformula NumericPAeqTerm.domainTemplate).isUFormula
  rw [guardedExsCode,substs_ex (IsUFormula.and.mpr ⟨hd,hp.isUFormula⟩),
    substs_and hd hp.isUFormula,domainTemplate_targetSubst hw]
  rfl
#print axioms domainTemplate_targetSubst
#print axioms equalityTail_targetSubst
#print axioms equalityCode_targetSubst
#print axioms guardedAllCode_targetSubst
#print axioms guardedExsCode_targetSubst
end M6.PA.NumericPAeqFormula

