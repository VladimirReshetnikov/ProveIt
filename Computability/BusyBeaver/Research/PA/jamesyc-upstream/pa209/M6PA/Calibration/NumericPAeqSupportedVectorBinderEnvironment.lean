module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedVectorBinderSyntax
@[expose] public section
namespace M6.PA.NumericPAeqSupportedVectorRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem vectorEnvironment_qVec {s r b f a w t body x:V}
    (h:SupportedVectorEnvironment s r b f a w t) (hx:IsSemiterm language 0 x)
    (hp:IsSemiterm Presentation.language (s+1) body) (hs:FreeSupported (len f) body):
    SupportedVectorEnvironment (s+1) (r+1) (x∷b) f (x∷a) (qVec Presentation.language w) body := by
  exact ⟨h.1.adjoin hx,h.2.1,h.2.2.1.adjoin hx,hp,h.2.2.2.2.1.qVec,hs,
    (vectorFreeSupported_qVec ⟨h.2.2.2.2.1.isUTerm,h.2.2.2.2.2.2⟩).2⟩
#print axioms vectorEnvironment_qVec
end M6.PA.NumericPAeqSupportedVectorRealization
