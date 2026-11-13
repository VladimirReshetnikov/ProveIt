module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaRealization
public import M6PA.Calibration.RelationalPredicateBinaryEmptyRequested
@[expose] public section
namespace M6.PA.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueVectorRealization
open RelationalPredicateBinary RelationalSource.Numeric ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def singletonInput (f u x:V):V :=
  qqAnd (NumericPAeqValueDomainGuard.guard f (len f)) (valueSyntax (NumericPAeqTerm.parameters 0 f x) u)
theorem singletonInput_valid {f u x:V} (hf:IsSemitermVec language (len f) 0 f)
    (hu:IsSemiterm Presentation.language 0 u) (hs:FreeSupported (len f) u) (hx:IsSemiterm language 0 x):
    IsFormula language (singletonInput f u x) := by
  refine IsSemiformula.and.mpr ⟨NumericPAeqValueDomainGuard.guard_vector_isSemiformula hf,?_⟩
  apply valueSyntax_supported_isSemiformula
  exact ⟨by simpa [ParametersValid] using And.intro (show IsSemitermVec language (0:V) 0 0 by simp) (And.intro hf hx),hu,by simpa using hs⟩
noncomputable def singletonInputProof (F D P:SF (V:=V) 0):
    ND.Proof (T:=(∅:Theory language).internalize V) ∅
      ((F ⋏ (D ⋏ P)) 🡒 ((⊤ ⋏ F) ⋏ (((⊤ ⋏ D) ⋏ F) ⋏ (⊤ ⋏ (D ⋏ P))))) := by
  apply ND.impIntro
  have h : ND.Proof (T:=(∅:Theory language).internalize V) (insert (∼(F ⋏ (D ⋏ P))) ∅) (F ⋏ (D ⋏ P)) := ND.assumption _ (by simp)
  have truth : ND.Proof (T:=(∅:Theory language).internalize V) (insert (∼(F ⋏ (D ⋏ P))) ∅) ⊤ := TDerivation.verum
  exact ND.andIntro (ND.andIntro truth (ND.andLeft h))
    (ND.andIntro (ND.andIntro (ND.andIntro truth (ND.andLeft (ND.andRight h))) (ND.andLeft h))
      (ND.andIntro truth (ND.andRight h)))
theorem singletonInput_certificate {f u x:V} (hf:IsSemitermVec language (len f) 0 f)
    (hu:IsSemiterm Presentation.language 0 u) (hs:FreeSupported (len f) u) (hx:IsSemiterm language 0 x)
    (native lo z:V) (hc:FormulaCovered 0 native lo z
      (imp language (singletonInput f u x) (vectorInput 1 0 0 f (x∷0) (u∷0)))):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (singletonInput f u x) (vectorInput 1 0 0 f (x∷0) (u∷0)))+1 := by
  obtain ⟨tail,he⟩ := valueSyntax_domain_shape (NumericPAeqTerm.parameters 0 f x) u hu.isUTerm
  simp only [parameters_result] at he
  have hv := (IsSemiformula.and.mp (singletonInput_valid hf hu hs hx)).2
  rw [he] at hv
  let F:SF (V:=V) 0 := ⟨NumericPAeqValueDomainGuard.guard f (len f),NumericPAeqValueDomainGuard.guard_vector_isSemiformula hf⟩
  let D:SF (V:=V) 0 := ⟨domainCode x,(IsSemiformula.and.mp hv).1⟩
  let P:SF (V:=V) 0 := ⟨tail,(IsSemiformula.and.mp hv).2⟩
  have gd : NumericPAeqValueDomainGuard.guard (x∷0) (1:V)=qqAnd qqVerum (domainCode x) := by
    simpa using NumericPAeqValueDomainGuard.guard_succ (x∷0) (0:V)
  have gv : NumericPAeqValueRealizationGuard.guard 0 f (u∷0) (x∷0) (1:V)=
      qqAnd qqVerum (valueSyntax (NumericPAeqTerm.parameters 0 f x) u) := by
    simpa [NumericPAeqValueRealizationGuard.entry] using NumericPAeqValueRealizationGuard.guard_succ (0:V) f (u∷0) (x∷0) (0:V)
  have hshape : imp language (singletonInput f u x) (vectorInput 1 0 0 f (x∷0) (u∷0))=
      ((F ⋏ (D ⋏ P)) 🡒 ((⊤ ⋏ F) ⋏ (((⊤ ⋏ D) ⋏ F) ⋏ (⊤ ⋏ (D ⋏ P))))).val := by
    simp only [singletonInput,vectorInput,inputDomain,
      gd,gv,NumericPAeqValueDomainGuard.guard_zero,he,
      Bootstrapping.Semiformula.val_imp,Bootstrapping.Semiformula.val_and,Bootstrapping.Semiformula.val_verum,F,D,P]
  rw [hshape] at hc ⊢
  exact empty_requested_certificate _ (singletonInputProof F D P) native lo z hc
#print axioms singletonInput_valid
#print axioms singletonInputProof
#print axioms singletonInput_certificate
end M6.PA.NumericPAeqFormulaRealization

