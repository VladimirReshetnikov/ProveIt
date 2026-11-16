module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateVariableCalibration
public import M6PA.Calibration.FoundationPAeqCodeSubstitutionAgreement
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate.Variable
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

private theorem eq_quote :
    (⌜(RelationalSource.ND.eq (.bvar 0) (.bvar 1) : RelationalSource.Ordinal.Formula 2)⌝:V)=
      qqRel 2 0 (qqBvar 0∷(qqBvar 1∷0)) := by
  have h := FFL.FirstOrder.Semiformula.quote_rel (V:=V) («L» := RelationalSource.language)
    RelationalSource.Relation.eq ![(.bvar 0 : Semiterm L Nat 2),.bvar 1]
  simpa [RelationalSource.ND.eq,SemitermVec.val,Matrix.vecHead,Matrix.vecTail,
    FFL.FirstOrder.Semiterm.typed_quote_bvar,Bootstrapping.Semiterm.bvar,GödelQuote.quote,Encodable.encode,FFL.FirstOrder.Semiterm.typedQuote,gödelQuoteRel,RelationalSource.languageEncodable,RelationalSource.relationEncodable] using h

private theorem domain_qVec (x : V) (hx:IsSemiterm L 0 x) :
    subst L (qVec L (x∷0)) (⌜domainTemplate⌝:V)=domainCode (qqBvar 0) := by
  apply FoundationPAeqCode.subst_agree_on_bound
    (n:=1) (m:=1) (k:=2) (l:=1) (p:=(⌜domainTemplate⌝:V))
    (by simpa using (show IsSemiformula L (1:V) (⌜domainTemplate⌝:V) by simp))
    (by convert (IsSemitermVec.singleton.mpr hx).qVec using 1 <;> norm_num)
    (by simp) (by simp) (by simp)
  intro i hi
  have he : i=0 := by simpa using hi
  subst i; simp [qVec]

theorem variableTotalityCode_constructor (x : V) (hx:IsSemiterm L 0 x) :
    variableTotalityCode x=imp L (domainCode x)
      (qqExs (variableValue (qqBvar 0) (termBShift L x))) := by
  have hd : IsSemiformula L (1:V) (⌜domainTemplate⌝:V) := by simp
  have he : IsUFormula L (qqRel 2 0 (qqBvar 0∷(qqBvar 1∷0:V))) := by simp
  have hb : (⌜body⌝:V)=imp L (⌜domainTemplate⌝:V)
      (qqExs (qqAnd (⌜domainTemplate⌝:V) (qqRel 2 0 (qqBvar 0∷(qqBvar 1∷0))))) := by
    simp only [body,FFL.FirstOrder.Semiformula.quote_def,LCWQIsoGödelQuote.imply,
      LCWQIsoGödelQuote.exs,LCWQIsoGödelQuote.and]
    change imp L _ (qqExs (qqAnd _ (⌜(RelationalSource.ND.eq (.bvar 0) (.bvar 1) : RelationalSource.Ordinal.Formula 2)⌝:V)))=_
    rw [eq_quote]
    have hd2 : (⌜(RelationalSource.Ordinal.domain (.bvar 0) : RelationalSource.Ordinal.Formula 2)⌝:V)=
        (⌜domainTemplate⌝:V) := by
      calc
        _ = (domainCode (qqBvar 0):V) := by
          simpa using (domainCode_quote (V:=V) (.bvar 0 : RelationalSource.Ordinal.Term 2)).symm
        _ = _ := by
          simpa [domainTemplate] using (domainCode_quote (V:=V) (.bvar 0 : RelationalSource.Ordinal.Term 1))
    change imp L (⌜domainTemplate⌝:V) (qqExs (qqAnd (⌜(RelationalSource.Ordinal.domain (.bvar 0) : RelationalSource.Ordinal.Formula 2)⌝:V) _))=_
    rw [hd2]
    rfl
  unfold variableTotalityCode templateOne substs1
  rw [hb]
  rw [imp,substs_or (hd.neg.isUFormula) (by simp [hd.isUFormula,he]),
    substs_neg hd (IsSemitermVec.singleton.mpr hx),
    substs_ex (by simp [hd.isUFormula,he]),substs_and hd.isUFormula he,domain_qVec x hx]
  congr 2
  simp [variableValue,equalityCode,templateTwo,equalityTemplate,substs_rel,
    qVec,termSubstVec_cons₁,hx.isUTerm]
  rw [eq_quote]
  simp [substs_rel]

#print axioms variableTotalityCode_constructor
end M6.PA.RelationalPredicateTemplate.Variable
