module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSingletonInput
@[expose] public section
namespace M6.PA.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueVectorRealization
open RelationalPredicateBinary RelationalSource.Numeric ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def oneEntryInput (r b f u x:V):V :=
  qqAnd (inputDomain r b f) (valueSyntax (NumericPAeqTerm.parameters b f x) u)
theorem oneEntryInput_valid {r b f u x:V} (hb:IsSemitermVec language r 0 b)
    (hf:IsSemitermVec language (len f) 0 f) (hu:IsSemiterm Presentation.language r u)
    (hs:FreeSupported (len f) u) (hx:IsSemiterm language 0 x):IsFormula language (oneEntryInput r b f u x) := by
  refine IsSemiformula.and.mpr ⟨NumericPAeqSupportedValueTotality.inputDomain_valid ⟨hb,hf,hu,hs⟩,?_⟩
  apply valueSyntax_supported_isSemiformula
  exact ⟨by simpa [ParametersValid] using And.intro hb (And.intro hf hx),hu,by simpa using hs⟩
noncomputable def oneEntryInputProof (B F D P:SF (V:=V) 0):
    ND.Proof (T:=(∅:Theory language).internalize V) ∅
      (((B ⋏ F) ⋏ (D ⋏ P)) 🡒 ((B ⋏ F) ⋏ (((⊤ ⋏ D) ⋏ F) ⋏ (⊤ ⋏ (D ⋏ P))))) := by
  apply ND.impIntro
  have h : ND.Proof (T:=(∅:Theory language).internalize V) (insert (∼((B ⋏ F) ⋏ (D ⋏ P))) ∅) ((B ⋏ F) ⋏ (D ⋏ P)) := ND.assumption _ (by simp)
  have truth : ND.Proof (T:=(∅:Theory language).internalize V) (insert (∼((B ⋏ F) ⋏ (D ⋏ P))) ∅) ⊤ := TDerivation.verum
  exact ND.andIntro (ND.andLeft h)
    (ND.andIntro (ND.andIntro (ND.andIntro truth (ND.andLeft (ND.andRight h))) (ND.andRight (ND.andLeft h)))
      (ND.andIntro truth (ND.andRight h)))
theorem oneEntryInput_certificate {r b f u x:V} (hb:IsSemitermVec language r 0 b)
    (hf:IsSemitermVec language (len f) 0 f) (hu:IsSemiterm Presentation.language r u)
    (hs:FreeSupported (len f) u) (hx:IsSemiterm language 0 x)
    (native lo z:V) (hc:FormulaCovered 0 native lo z
      (imp language (oneEntryInput r b f u x) (vectorInput 1 r b f (x∷0) (u∷0)))):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (oneEntryInput r b f u x) (vectorInput 1 r b f (x∷0) (u∷0)))+1 := by
  obtain ⟨tail,he⟩ := valueSyntax_domain_shape (NumericPAeqTerm.parameters b f x) u hu.isUTerm
  simp only [parameters_result] at he
  have hv := (IsSemiformula.and.mp (oneEntryInput_valid hb hf hu hs hx)).2
  rw [he] at hv
  let B:SF (V:=V) 0 := ⟨NumericPAeqValueDomainGuard.guard b r,NumericPAeqValueDomainGuard.guard_vector_isSemiformula hb⟩
  let F:SF (V:=V) 0 := ⟨NumericPAeqValueDomainGuard.guard f (len f),NumericPAeqValueDomainGuard.guard_vector_isSemiformula hf⟩
  let D:SF (V:=V) 0 := ⟨domainCode x,(IsSemiformula.and.mp hv).1⟩
  let P:SF (V:=V) 0 := ⟨tail,(IsSemiformula.and.mp hv).2⟩
  have gd : NumericPAeqValueDomainGuard.guard (x∷0) (1:V)=qqAnd qqVerum (domainCode x) := by
    simpa using NumericPAeqValueDomainGuard.guard_succ (x∷0) (0:V)
  have gv : NumericPAeqValueRealizationGuard.guard b f (u∷0) (x∷0) (1:V)=
      qqAnd qqVerum (valueSyntax (NumericPAeqTerm.parameters b f x) u) := by
    simpa [NumericPAeqValueRealizationGuard.entry] using NumericPAeqValueRealizationGuard.guard_succ b f (u∷0) (x∷0) (0:V)
  have hshape : imp language (oneEntryInput r b f u x) (vectorInput 1 r b f (x∷0) (u∷0))=
      (((B ⋏ F) ⋏ (D ⋏ P)) 🡒 ((B ⋏ F) ⋏ (((⊤ ⋏ D) ⋏ F) ⋏ (⊤ ⋏ (D ⋏ P))))).val := by
    simp only [oneEntryInput,vectorInput,inputDomain,gd,gv,he,
      Bootstrapping.Semiformula.val_imp,Bootstrapping.Semiformula.val_and,Bootstrapping.Semiformula.val_verum,B,F,D,P]
  rw [hshape] at hc ⊢
  exact empty_requested_certificate _ (oneEntryInputProof B F D P) native lo z hc
#print axioms oneEntryInput_valid
#print axioms oneEntryInputProof
#print axioms oneEntryInput_certificate
end M6.PA.NumericPAeqFormulaRealization
