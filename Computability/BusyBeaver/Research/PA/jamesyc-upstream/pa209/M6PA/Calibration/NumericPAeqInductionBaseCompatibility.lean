module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqInductionInterpretationSyntax
public import M6PA.Calibration.NumericPAeqFormulaUniversalCurry
public import M6PA.Calibration.NumericPAeqFormulaInstanceForward
@[expose] public section
namespace M6.PA.NumericPAeqInductionInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaRealization NumericPAeqFormulaLogical NumericPAeqValueTotality
open NumericPAeqTerm (targetShiftTerms targetShiftTerms_valid targetShiftTerms_length)
open RelationalSource.Numeric ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def baseCompatibilityCode (f p:V):V :=
  imp language (qqAnd (freeDomain f) (zeroValue f p)) (qqAll (imp language zeroDomain (property f p)))
theorem base_compatibility_certificate {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p)
    (native lo z:V) (hc:FormulaCovered 0 native lo z (baseCompatibilityCode f p)):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z) (baseCompatibilityCode f p)+1 := by
  have hF := freeDomain_valid hf
  have hB := zeroValue_valid hf hp hs
  have hP := property_valid hf hp hs
  apply guarded_universal_certificate _ _ native lo z (IsSemiformula.and.mpr ⟨hF,hB⟩)
    (IsSemiformula.imp.mpr ⟨zeroDomain_valid,hP⟩) hc
  intro native lo z hc
  rw [shift_and hF.isUFormula hB.isUFormula,freeDomain_shift hf,zeroValue_shift hf hp hs,
    free_imp_code zeroDomain_valid hP,zeroDomain_free,property_free hf hp hs] at hc ⊢
  let fs := targetShiftTerms f
  let x:V := qqFvar 0
  have hf' : IsSemitermVec language (len fs) 0 fs := by simpa [fs,targetShiftTerms_length hf] using targetShiftTerms_valid hf
  have hs' : FreeSupported (len fs) p := by simpa [fs,targetShiftTerms_length hf] using hs
  have hx : IsSemiterm language 0 x := by simp [x]
  let D := qqAnd (NumericPAeqTerm.domainCode x) (NumericPAeqTerm.zeroCode x)
  let F := freeDomain fs
  let B := zeroValue fs p
  let P := originalFormula (x∷0) fs p
  have hD : IsFormula language D := IsSemiformula.and.mpr ⟨NumericPAeqTerm.domainCode_isSemiformula hx,NumericPAeqTerm.zeroCode_isSemiformula hx⟩
  have hF' : IsFormula language F := freeDomain_valid hf'
  have hB' : IsFormula language B := zeroValue_valid hf' hp hs'
  have hP' : IsFormula language P := originalFormula_valid (singleton_environment ⟨hf',hp,by simp,hs',zero_supported _,hx⟩)
  have hBi : IsFormula language (biCode B P) := IsSemiformula.and.mpr ⟨IsSemiformula.imp.mpr ⟨hB',hP'⟩,IsSemiformula.imp.mpr ⟨hP',hB'⟩⟩
  apply source_certificate_mp (imp language (qqAnd F D) (biCode B P)) (imp language (qqAnd F B) (imp language D P)) native lo z
    (IsSemiformula.imp.mpr ⟨IsSemiformula.and.mpr ⟨hF',hD⟩,hBi⟩)
    (IsSemiformula.imp.mpr ⟨IsSemiformula.and.mpr ⟨hF',hB'⟩,IsSemiformula.imp.mpr ⟨hD,hP'⟩⟩) hc
  · intro native lo z hc
    exact zero_instance_formula_certificate hf' hp hs' hx native lo z hc
  · intro native lo z hc
    exact instanceForward_requested_certificate F D B P native lo z hF' hD hB' hP' hc
#print axioms base_compatibility_certificate
end M6.PA.NumericPAeqInductionInterpretation

