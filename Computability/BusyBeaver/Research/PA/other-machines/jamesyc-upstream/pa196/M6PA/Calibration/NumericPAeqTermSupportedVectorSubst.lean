module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermFreeSupportSubstitution
public import M6PA.Calibration.NumericPAeqTermSupportedBoundInstance
@[expose] public section
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem supported_coverage_subst {s r n param w t : V}
    (hp : ParametersValid r n param) (ht : IsSemiterm Presentation.language s t)
    (hw : IsSemitermVec Presentation.language s r w)
    (hs : FreeSupported (len (nth param 1)) t)
    (hws : ∀ i<s, FreeSupported (len (nth param 1)) (nth w i)) :
    SupportedTermCovered r n param (termSubst Presentation.language w t) :=
  ⟨hp,hw.termSubst ht,freeSupported_subst ht hw hs hws⟩

theorem valueSyntax_supported_vectorSubst_isSemiformula {s r n param w t : V}
    (hp : ParametersValid r n param) (ht : IsSemiterm Presentation.language s t)
    (hw : IsSemitermVec Presentation.language s r w)
    (hs : FreeSupported (len (nth param 1)) t)
    (hws : ∀ i<s, FreeSupported (len (nth param 1)) (nth w i)) :
    IsSemiformula language n (valueSyntax param (termSubst Presentation.language w t)) :=
  valueSyntax_supported_isSemiformula (supported_coverage_subst hp ht hw hs hws)

theorem valueSyntax_supported_vectorSubst_targetSubst {s r n m param w v t : V}
    (hp : ParametersValid r n param) (ht : IsSemiterm Presentation.language s t)
    (hw : IsSemitermVec Presentation.language s r w)
    (hs : FreeSupported (len (nth param 1)) t)
    (hws : ∀ i<s, FreeSupported (len (nth param 1)) (nth w i))
    (hv : IsSemitermVec language n m v) :
    subst language v (valueSyntax param (termSubst Presentation.language w t))=
      valueSyntax (targetSubstParameters v param) (termSubst Presentation.language w t) :=
  valueSyntax_supported_targetSubst (supported_coverage_subst hp ht hw hs hws) hv

theorem valueSyntax_supported_vectorSubst_bound_instance {s r b f w t n x : V}
    (hb : IsSemitermVec language r 0 b) (hf : IsSemitermVec language (len f) 0 f)
    (ht : IsSemiterm Presentation.language s t) (hw : IsSemitermVec Presentation.language s r w)
    (hs : FreeSupported (len f) t) (hws : ∀ i<s, FreeSupported (len f) (nth w i))
    (hx : IsSemiterm language n x) :
    substs1 language x (valueSyntax (parameters b f (qqBvar 0)) (termSubst Presentation.language w t))=
      valueSyntax (parameters b f x) (termSubst Presentation.language w t) :=
  valueSyntax_supported_bound_instance hb hf (hw.termSubst ht) (freeSupported_subst ht hw hs hws) hx
#print axioms supported_coverage_subst
#print axioms valueSyntax_supported_vectorSubst_isSemiformula
#print axioms valueSyntax_supported_vectorSubst_targetSubst
#print axioms valueSyntax_supported_vectorSubst_bound_instance
end M6.PA.NumericPAeqTerm
