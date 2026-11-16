module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaEnvironment
public import M6PA.Calibration.NumericPAeqValueDomainGuardCollection
public import M6PA.Calibration.FoundationRelationalSequentConnectiveNormalization
@[expose] public section
namespace M6.PA.NumericPAeqRepeatedEnvironment
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Numeric NumericPAeqTerm
open ActualCertificateConstructors.Dominated ActualCertificateEquivalence ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
/-- This is the pinned arithmetic HFS repetition, not host-list replication. -/
noncomputable abbrev environment (x k:V):V := repeatVec x k
 theorem environment_graph (out x k:V):repeatVecDef.val.Evalb ![out,x,k] ↔ out=environment x k := by simp
 theorem environment_exists_unique (x k:V):∃! out,repeatVecDef.val.Evalb ![out,x,k] := by
  simp only [environment_graph]
  exact ⟨environment x k,rfl,fun _ h=>h⟩
 theorem environment_length (x k:V):len (environment x k)=k := by simp
 theorem environment_nth {x k i:V} (hi:i<k):nth (environment x k) i=x := nth_repeatVec x k hi
 theorem environment_valid {n x:V} (hx:IsSemiterm language n x) (k:V):
    IsSemitermVec language k n (environment x k) := NumericPAeqFormula.repeatedTermVector hx k

 theorem domain_collection_certificate (x k param:V) (hx:IsSemiterm language 0 x):
    ∃code,verifyValue code=wim (translate param (domainCode x))
      (translate param (NumericPAeqValueDomainGuard.guard (environment x k) k))+1 := by
  apply NumericPAeqValueDomainGuard.guard_collection_certificate _ param _ k 0
  · intro i hi; simpa only [environment_nth hi] using hx
  · intro i hi
    rw [environment_nth hi]
    let out := (Context.assumption (by simp) : Context [translate param (domainCode x)] (translate param (domainCode x))).deduction.empty
    exact ⟨out.code,out.accepted⟩

 theorem domain_requested_certificate (x k g lo z:V) (hx:IsSemiterm language 0 x)
    (_hc:FormulaCovered 0 g lo z (imp language (domainCode x)
      (NumericPAeqValueDomainGuard.guard (environment x k) (len (environment x k))))):
    ∃code,verifyValue code=translate (parameters 0 g lo z)
      (imp language (domainCode x) (NumericPAeqValueDomainGuard.guard (environment x k) (len (environment x k))))+1 := by
  rw [environment_length]
  let param := parameters 0 g lo z
  obtain ⟨code,hcode⟩ := domain_collection_certificate x k param hx
  have hd := domainCode_isSemiformula hx
  have hg := NumericPAeqValueDomainGuard.guard_isSemiformula (environment x k) k 0
    (fun i hi=>by simpa only [environment_nth hi] using hx)
  obtain ⟨_,back,_,hback⟩ := translate_imp_certificates param _ _ hd.isUFormula hg.isUFormula
  let out := (⟨code,hcode⟩ : Certificate _).mp ⟨back,hback⟩
  exact ⟨out.code,out.accepted⟩
#print axioms environment_graph
#print axioms environment_exists_unique
#print axioms environment_valid
#print axioms domain_collection_certificate
#print axioms domain_requested_certificate
end M6.PA.NumericPAeqRepeatedEnvironment

