module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqBottomDomainProof
public import PA196.Arithmetic.Transport.RelationalClosedCertificateSupply
public import PA196.Arithmetic.Transport.NumericPAeqSourceCertificateMP
public import M6PA.Calibration.NumericPAeqFormulaOpeningLogic
public import PA196.Arithmetic.Transport.FoundationRelationalSequentRequestedUniversal
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqBottomDomain
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary RelationalSource.Numeric PA196.Arithmetic.Checker NumericPAeqValueTotality
open NumericPAeqFormulaRealization
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
noncomputable def domainRefutationMatrix :V:=imp L (⌜NumericPAeqTerm.domainTemplate⌝:V) qqFalsum
noncomputable def domainRefutationCode :V:=qqAll (domainRefutationMatrix (V:=V))
theorem domainRefutationMatrix_valid:IsSemiformula L 1 (domainRefutationMatrix (V:=V)):=by
  apply IsSemiformula.imp.mpr
  simp
theorem domainRefutation_valid:IsFormula L (domainRefutationCode (V:=V)):=by
  apply IsSemiformula.all.mpr
  simpa using domainRefutationMatrix_valid (V:=V)
theorem domainRefutationMatrix_free:
    free L (domainRefutationMatrix (V:=V))=imp L (NumericPAeqTerm.domainCode (qqFvar (0:V))) qqFalsum:=by
  rw [domainRefutationMatrix,free_imp_code (by simp) (by simp),free_domain_code]
  simp [free,substs1]
theorem domainRefutation_requested_certificate (native lo z:V)
    (hc:FormulaCovered 0 native lo z (domainRefutationCode (V:=V)))
    (child:∀g l z,FormulaCovered 0 g l z (imp L (NumericPAeqTerm.domainCode (qqFvar (0:V))) qqFalsum)→
      ∃code,verifyValue code=translate (parameters 0 g l z) (imp L (NumericPAeqTerm.domainCode (qqFvar (0:V))) qqFalsum)+1):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (domainRefutationCode (V:=V))+1:=by
  apply requested_universal_certificate _ native lo z domainRefutationMatrix_valid hc
  intro g l z hc
  rw [domainRefutationMatrix_free] at hc ⊢
  exact child g l z hc

theorem domain_contradiction_requested_certificate (native lo z:V)
    (hc:FormulaCovered 0 native lo z (imp L (domainRefutationCode (V:=V))
      (imp L (⌜ForwardRelational.zeroInhabited⌝:V) qqFalsum))):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (imp L (domainRefutationCode (V:=V))
      (imp L (⌜ForwardRelational.zeroInhabited⌝:V) qqFalsum))+1:=by
  let D:SF (V:=V) 1:=⟨(⌜NumericPAeqTerm.domainTemplate⌝:V),by simp⟩
  let Z:SF (V:=V) 1:=⟨(⌜NumericPAeqTerm.zeroTemplate⌝:V),by simp⟩
  have hz:(∃¹ (D ⋏ Z)).val=(⌜ForwardRelational.zeroInhabited⌝:V):=by
    simp [D,Z,ForwardRelational.zeroInhabited,NumericPAeqTerm.domainTemplate,NumericPAeqTerm.zeroTemplate]
  have he:((∀¹ (D 🡒 ⊥)) 🡒 ((∃¹ (D ⋏ Z)) 🡒 ⊥)).val=
      imp L (domainRefutationCode (V:=V)) (imp L (⌜ForwardRelational.zeroInhabited⌝:V) qqFalsum):=by
    change imp L (domainRefutationCode (V:=V)) (imp L (∃¹ (D ⋏ Z)).val qqFalsum)=_
    rw [hz]
  rw [←he] at hc ⊢
  exact empty_requested_certificate _ (domainContradiction D Z) native lo z hc
#print axioms domainRefutationMatrix_valid
#print axioms domainRefutationMatrix_free
#print axioms domainRefutation_requested_certificate
#print axioms domain_contradiction_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqBottomDomain

