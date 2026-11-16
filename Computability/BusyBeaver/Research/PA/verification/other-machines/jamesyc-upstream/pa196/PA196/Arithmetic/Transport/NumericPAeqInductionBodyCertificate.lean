module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqInductionBodyInterpretation
public import PA196.Arithmetic.Transport.NumericPAeqInductionBaseCompatibility
public import PA196.Arithmetic.Transport.NumericPAeqInductionStepCompatibility
public import PA196.Arithmetic.Transport.NumericPAeqOrdinalInductionShapeSupply
public import PA196.Arithmetic.Transport.NumericPAeqInductionCombineCertificate
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqInductionInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqValueTotality NumericPAeqInductionCombine
open RelationalSource.Numeric PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def guardedInductionBodyCode (f p:V):V :=
  imp language (freeDomain f) (formulaSyntax (NumericPAeqFormula.parameters 0 f) (FoundationPAeqCode.targetIndBody p))
theorem guarded_induction_body_certificate {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p)
    (native lo z:V) (hc:FormulaCovered 0 native lo z (guardedInductionBodyCode f p)):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z) (guardedInductionBodyCode f p)+1 := by
  let F := freeDomain f
  let B := zeroValue f p
  let S := NumericPAeqInductionStepTemplate.sourceStepCode (property f p) (successorProperty f p)
  let A := NumericPAeqOrdinalInductionShape.baseCode (property f p)
  let T := NumericPAeqOrdinalInductionShape.stepCode (property f p)
  let C := NumericPAeqOrdinalInductionShape.conclusionCode (property f p)
  have hP := property_valid hf hp hs
  have hO := NumericPAeqOrdinalInductionShape.inductionCode_isFormula hP
  have hC : IsFormula language C := (IsSemiformula.imp.mp hO).2
  have hA : IsFormula language A := (IsSemiformula.and.mp (IsSemiformula.imp.mp hO).1).1
  have hT : IsFormula language T := (IsSemiformula.and.mp (IsSemiformula.imp.mp hO).1).2
  have hF := freeDomain_valid hf
  have hB := zeroValue_valid hf hp hs
  have hv := NumericPAeqInductionStepTemplate.stepCode_valid hF hP (successorProperty_valid hf hp hs)
  have hS : IsFormula language S := (IsSemiformula.and.mp (IsSemiformula.imp.mp (IsSemiformula.imp.mp hv).2).1).2
  have hd := NumericPAeqTerm.domainCode_quote (V:=V) (.bvar 0 : RelationalSource.Ordinal.Term 1)
  change NumericPAeqTerm.domainCode (qqBvar 0)=(⌜NumericPAeqTerm.domainTemplate⌝:V) at hd
  have he : guardedInductionBodyCode f p=imp language F (imp language B (imp language S C)) := by
    rw [guardedInductionBodyCode,targetIndBody_interpretation hf hp hs]
    simp only [guardedAllCode,←hd]
    rfl
  rw [he] at hc ⊢
  let X := imp language (qqAnd F B) A
  let Y := imp language (qqAnd F S) T
  let Z := imp language (qqAnd A T) C
  let R := imp language F (imp language B (imp language S C))
  have hX : IsFormula language X := IsSemiformula.imp.mpr ⟨IsSemiformula.and.mpr ⟨hF,hB⟩,hA⟩
  have hY : IsFormula language Y := IsSemiformula.imp.mpr ⟨IsSemiformula.and.mpr ⟨hF,hS⟩,hT⟩
  have hZ : IsFormula language Z := hO
  have hR : IsFormula language R := IsSemiformula.imp.mpr ⟨hF,IsSemiformula.imp.mpr ⟨hB,IsSemiformula.imp.mpr ⟨hS,hC⟩⟩⟩
  have first : ∀ g l z, FormulaCovered 0 g l z (imp language Y (imp language Z R)) →
      ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 g l z) (imp language Y (imp language Z R))+1 := by
    intro g l z hc
    apply source_certificate_mp X _ g l z hX (IsSemiformula.imp.mpr ⟨hY,IsSemiformula.imp.mpr ⟨hZ,hR⟩⟩) hc
    · exact base_compatibility_certificate hf hp hs
    · intro g l z hc
      exact combine_requested_certificate F B S A T C g l z hF hB hS hA hT hC hc
  have second : ∀ g l z, FormulaCovered 0 g l z (imp language Z R) →
      ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 g l z) (imp language Z R)+1 := by
    intro g l z hc
    apply source_certificate_mp Y _ g l z hY (IsSemiformula.imp.mpr ⟨hZ,hR⟩) hc
    · exact step_compatibility_certificate hf hp hs
    · exact first
  apply source_certificate_mp Z R native lo z hZ hR hc
  · intro g l z hc
    exact NumericPAeqOrdinalInductionShape.inductionCode_requested_certificate _ g l z hP hc
  · exact second
#print axioms guarded_induction_body_certificate
end PA196.Arithmetic.Transport.NumericPAeqInductionInterpretation

