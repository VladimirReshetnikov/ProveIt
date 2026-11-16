module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqInductionSuccessorSyntax
public import M6PA.Calibration.NumericPAeqFormulaLogicalCurry
public import M6PA.Calibration.NumericPAeqSourceCertificateMP
@[expose] public section
namespace M6.PA.NumericPAeqInductionInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaRealization NumericPAeqFormulaLogical NumericPAeqValueTotality
open RelationalSource.Numeric ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def successorComparisonCode (f p x y:V):V :=
  imp language (freeDomain f)
    (imp language (qqAnd (NumericPAeqTerm.domainCode x) (qqAnd (NumericPAeqTerm.domainCode y) (NumericPAeqTerm.successorCode x y)))
      (biCode (substs1 language x (successorProperty f p)) (substs1 language y (property f p))))
theorem successor_comparison_certificate {f p x y:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p)
    (hx:IsSemiterm language 0 x) (hy:IsSemiterm language 0 y)
    (native lo z:V) (hc:FormulaCovered 0 native lo z (successorComparisonCode f p x y)):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z) (successorComparisonCode f p x y)+1 := by
  have he := oneEntry_environment (IsSemitermVec.singleton.mpr hx) hf hp successorReplacement_valid hs (successorReplacement_supported (len f)) hy
  let F := freeDomain f
  let D := qqAnd (NumericPAeqTerm.domainCode x) (qqAnd (NumericPAeqTerm.domainCode y) (NumericPAeqTerm.successorCode x y))
  let C := formulaComparison (x∷0) f (y∷0) (successorReplacement∷0) p
  have hF : IsFormula language F := freeDomain_valid hf
  have hD : IsFormula language D := IsSemiformula.and.mpr ⟨NumericPAeqTerm.domainCode_isSemiformula hx,
    IsSemiformula.and.mpr ⟨NumericPAeqTerm.domainCode_isSemiformula hy,NumericPAeqTerm.successorCode_isSemiformula hx hy⟩⟩
  have hC : IsFormula language C := formulaComparison_valid he
  have hshape : successorComparisonCode f p x y=imp language F (imp language D C) := by
    simp only [successorComparisonCode,successorProperty_instance hf hp hs hx,property_instance hf hp hs hy,F,D,C,formulaComparison,biCode]
  rw [hshape] at hc ⊢
  apply source_certificate_mp (imp language (qqAnd F D) C) (imp language F (imp language D C)) native lo z
    (IsSemiformula.imp.mpr ⟨IsSemiformula.and.mpr ⟨hF,hD⟩,hC⟩)
    (IsSemiformula.imp.mpr ⟨hF,IsSemiformula.imp.mpr ⟨hD,hC⟩⟩) hc
  · exact successor_instance_formula_certificate hf hp hs hx hy
  · intro native lo z hc
    exact curry_requested_certificate F D C native lo z hF hD hC hc
#print axioms successor_comparison_certificate
end M6.PA.NumericPAeqInductionInterpretation

