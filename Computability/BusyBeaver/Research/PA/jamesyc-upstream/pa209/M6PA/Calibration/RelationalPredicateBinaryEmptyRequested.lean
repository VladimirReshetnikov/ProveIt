module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateBinaryRequested
@[expose] public section
namespace M6.PA.RelationalPredicateBinary
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint RelationalSource.Numeric
open ActualCertificateConstructors.Dominated ActualCertificateEquivalence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
theorem empty_requested_certificate (q:SF (V:=V) 0)
    (d:ND.Proof (T:=(∅:Theory L).internalize V) ∅ q)
    (g lo z:V) (hc:FormulaCovered 0 g lo z q.val):
    ∃code,verifyValue code=translate (parameters 0 g lo z) q.val+1 := by
  apply singleton_requested_certificate (⊤:SF (V:=V) 0) q (ND.weaken d (by intro x hx; simpa using hx)) g lo z hc
  intro g lo z _
  let out := truthCertificate (V:=V)
  exact ⟨out.code,by simpa only [Bootstrapping.Semiformula.val_verum,translate_verum,zero_add] using out.accepted⟩
#print axioms empty_requested_certificate
end M6.PA.RelationalPredicateBinary

