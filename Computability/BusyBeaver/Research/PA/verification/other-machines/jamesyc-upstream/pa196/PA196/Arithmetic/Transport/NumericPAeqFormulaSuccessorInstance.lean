module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqFormulaOneEntryRealization
public import PA196.Arithmetic.Transport.NumericPAeqInductionSuccessorValueCertificate
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqFormulaRealization

namespace PA196.Arithmetic.Transport.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueVectorRealization NumericPAeqValueCoherence
open RelationalPredicateBinary RelationalSource.Numeric PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def successorReplacement : V := qqFunc 1 1 (qqBvar 0∷0)
noncomputable def successorInstanceInput (f x y:V):V :=
  qqAnd (NumericPAeqValueDomainGuard.guard f (len f)) (qqAnd (domainCode x) (qqAnd (domainCode y) (successorCode x y)))
noncomputable def successorInstanceCode (f p x y:V):V :=
  imp language (successorInstanceInput f x y) (formulaComparison (x∷0) f (y∷0) (successorReplacement∷0) p)
theorem successorReplacement_valid : IsSemiterm Presentation.language (1:V) successorReplacement := by
  simp [successorReplacement]
theorem successorReplacement_supported (l:V):FreeSupported l successorReplacement := by
  apply (freeSupported_func (show Presentation.language.IsFunc (1:V) 1 by simp)
    (show IsUTermVec Presentation.language (1:V) (qqBvar 0∷0) by simp)).mpr
  intro i hi
  have he : i=0 := by simpa using hi
  subst i; simp [freeSupported_bvar]
noncomputable def successorDomainProof (F D A:SF (V:=V) 0):
    ND.Proof (T:=(∅:Theory language).internalize V) ∅ ((F ⋏ (D ⋏ A)) 🡒 ((⊤ ⋏ D) ⋏ F)) := by
  apply ND.impIntro
  have h : ND.Proof (T:=(∅:Theory language).internalize V) (insert (∼(F ⋏ (D ⋏ A))) ∅) (F ⋏ (D ⋏ A)) := ND.assumption _ (by simp)
  have truth : ND.Proof (T:=(∅:Theory language).internalize V) (insert (∼(F ⋏ (D ⋏ A))) ∅) ⊤ := TDerivation.verum
  exact ND.andIntro (ND.andIntro truth (ND.andLeft (ND.andRight h))) (ND.andLeft h)
theorem successor_instance_formula_certificate {f p x y:V}
    (hf:IsSemitermVec language (len f) 0 f) (hp:IsSemiformula Presentation.language 1 p)
    (hs:NumericPAeqFormula.FreeSupported (len f) p) (hx:IsSemiterm language 0 x) (hy:IsSemiterm language 0 y)
    (native lo z:V) (hc:FormulaCovered 0 native lo z (successorInstanceCode f p x y)):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z) (successorInstanceCode f p x y)+1 := by
  have hb := IsSemitermVec.singleton.mpr hx
  have hu := successorReplacement_valid (V:=V)
  have hus := successorReplacement_supported (len f)
  have he := oneEntry_environment hb hf hp hu hs hus hy
  let F := NumericPAeqValueDomainGuard.guard f (len f)
  let A := qqAnd (domainCode x) (qqAnd (domainCode y) (successorCode x y))
  let O := valueSyntax (NumericPAeqTerm.parameters (x∷0) f y) successorReplacement
  have hF : IsFormula language F := NumericPAeqValueDomainGuard.guard_vector_isSemiformula hf
  have hA : IsFormula language A := IsSemiformula.and.mpr ⟨domainCode_isSemiformula hx,
    IsSemiformula.and.mpr ⟨domainCode_isSemiformula hy,successorCode_isSemiformula hx hy⟩⟩
  have hH : IsFormula language (successorInstanceInput f x y) := IsSemiformula.and.mpr ⟨hF,hA⟩
  have hI := oneEntryInput_valid hb hf hu hus hy
  have hD := NumericPAeqSupportedValueTotality.inputDomain_valid ⟨hb,hf,hu,hus⟩
  have hO : IsFormula language O := (IsSemiformula.and.mp hI).2
  apply source_implication_compose _ (oneEntryInput 1 (x∷0) f successorReplacement y) _ native lo z
    hH hI (formulaComparison_valid he) hc
  · intro native lo z hc
    apply source_implication_pair _ (inputDomain 1 (x∷0) f) O native lo z hH hD hO hc
    · intro native lo z hc
      let FF:SF (V:=V) 0 := ⟨F,hF⟩
      let DD:SF (V:=V) 0 := ⟨domainCode x,domainCode_isSemiformula hx⟩
      let AA:SF (V:=V) 0 := ⟨qqAnd (domainCode y) (successorCode x y),(IsSemiformula.and.mp hA).2⟩
      have gd : NumericPAeqValueDomainGuard.guard (x∷0) (1:V)=qqAnd qqVerum (domainCode x) := by
        simpa using NumericPAeqValueDomainGuard.guard_succ (x∷0) (0:V)
      have eqn : imp language (successorInstanceInput f x y) (inputDomain 1 (x∷0) f)=
          ((FF ⋏ (DD ⋏ AA)) 🡒 ((⊤ ⋏ DD) ⋏ FF)).val := by
        simp only [successorInstanceInput,inputDomain,gd,Bootstrapping.Semiformula.val_imp,
          Bootstrapping.Semiformula.val_and,Bootstrapping.Semiformula.val_verum,FF,DD,AA,F]
      rw [eqn] at hc ⊢
      exact empty_requested_certificate _ (successorDomainProof FF DD AA) native lo z hc
    · intro native lo z hc
      apply source_implication_compose _ A O native lo z hH hA hO hc
      · intro native lo z _
        exact source_conjunction_projection (RelationalSource.Numeric.parameters 0 native lo z) F A hF.isUFormula hA.isUFormula false
      · intro native lo z hc
        exact NumericPAeqInductionSuccessorValue.successor_value_requested_certificate x y f native lo z hx hy hf hc
  · exact one_entry_formula_certificate hb hf hp hu hs hus hy
#print axioms successorReplacement_valid
#print axioms successorReplacement_supported
#print axioms successorDomainProof
#print axioms successor_instance_formula_certificate
end PA196.Arithmetic.Transport.NumericPAeqFormulaRealization

