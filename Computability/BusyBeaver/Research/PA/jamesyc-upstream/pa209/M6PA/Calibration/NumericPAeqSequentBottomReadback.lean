module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSequentDerivationInvariant
public import M6PA.Calibration.NumericPAeqSourceCertificateMP
@[expose] public section
namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqInductionInterpretation NumericPAeqValueTotality
open ActualCertificateConstructors.Dominated ActualCertificateEquivalence ActualCheckerBlueprint
open RelationalSource.Numeric (translate translate_imp_certificates)
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem bottom_supported {f:V} (hf:IsSemitermVec language (len f) 0 f):
    SupportedSet (parameters 0 f) {(qqFalsum:V)}:=by
  intro p hp
  have he:p=(qqFalsum:V):=by simpa using hp
  subst p
  refine ⟨?_,by simp,?_⟩
  · simpa [ParametersValid] using hf
  · simp [FreeSupported,freeBound_falsum]
theorem bottom_fold_certificate (native f:V) (hf:IsSemitermVec language (len f) 0 f):
    ∃code,verifyValue code=wim (translate native (sequentCode (parameters 0 f) {(qqFalsum:V)}))
      (translate native (qqFalsum:V))+1:=by
  apply sequent_eliminate_certificate native _ _ _ (bottom_supported hf)
  intro p hp
  have he:p=(qqFalsum:V):=by simpa using hp
  subst p
  rw [formulaSyntax_falsum]
  let out := (Context.assumption (Γ:=[translate native (qqFalsum:V)]) (a:=translate native (qqFalsum:V)) (by simp)).deduction.empty
  exact ⟨out.code,out.accepted⟩
theorem bottom_guarded_readback {f:V} (hf:IsSemitermVec language (len f) 0 f)
    (child:RequestedCertificate f {(qqFalsum:V)})
    (native lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z
      (imp language (freeDomain f) qqFalsum)):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (freeDomain f) qqFalsum)+1:=by
  have hH:=freeDomain_valid hf
  have hS:=sequent_valid _ _ 0 0 (bottom_supported hf)
  have hB:IsFormula language (qqFalsum:V):=by simp
  apply source_implication_compose (freeDomain f) (sequentCode (parameters 0 f) {(qqFalsum:V)})
    qqFalsum native lo z hH hS hB hc
  · exact child
  · intro g l z _
    let param:=RelationalSource.Numeric.parameters 0 g l z
    obtain ⟨code,hcode⟩:=bottom_fold_certificate param f hf
    obtain ⟨_,back,_,hback⟩:=translate_imp_certificates param _ _ hS.isUFormula hB.isUFormula
    let out:Certificate (translate param (imp language (sequentCode (parameters 0 f) {(qqFalsum:V)}) qqFalsum)):=
      (⟨code,hcode⟩:Certificate _).mp ⟨back,hback⟩
    exact ⟨out.code,out.accepted⟩
#print axioms bottom_supported
#print axioms bottom_fold_certificate
#print axioms bottom_guarded_readback
end M6.PA.NumericPAeqFormula.Sequent

