module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermVectorSubstTarget
public import M6PA.Calibration.NumericPAeqValueBoundInstance
@[expose] public section
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem valueSyntax_vectorSubst_bound_instance {s r b f t w n x : V}
    (hb : IsSemitermVec language r 0 b)
    (hf : IsSemitermVec language (len f) 0 f)
    (ht : IsSemiterm Presentation.language s t) (hw : IsSemitermVec Presentation.language s r w)
    (htBound : t≤len f) (hwBound : ∀ i<s, nth w i≤len f) (hx : IsSemiterm language n x) :
    substs1 language x (valueSyntax (parameters b f (qqBvar 0)) (termSubst Presentation.language w t))=
      valueSyntax (parameters b f x) (termSubst Presentation.language w t) := by
  have hf1 : IsSemitermVec language (len f) 1 f := by
    rw [←shiftTerms_zero_arity hf]
    simpa only [shiftTerms_length hf,zero_add] using shiftTerms_isSemitermVec hf
  have hb1 : IsSemitermVec language r 1 b := by
    rw [←shiftTerms_zero_arity hb]
    simpa using shiftTerms_isSemitermVec hb
  have h : SubstitutionCovered s r 1 (parameters b f (qqBvar 0)) w t := by
    refine ⟨?_,ht,?_,hw,?_⟩
    · simpa [ParametersValid] using And.intro hb1
        (And.intro hf1 (show IsSemiterm language 1 (qqBvar 0) by simp))
    · simpa using htBound
    · simpa using hwBound
  have hxv : IsSemitermVec language 1 n (x∷0) := IsSemitermVec.singleton.mpr hx
  change subst language (x∷0) _=_
  rw [valueSyntax_vectorSubst_targetSubst h hxv]
  simp only [targetSubstParameters,parameters_bound,parameters_free,parameters_result,substTerms_zero_arity _ hf,substTerms_zero_arity _ hb]
  simp [RelationalPredicateTemplate.substTerms]
#print axioms valueSyntax_vectorSubst_bound_instance
end M6.PA.NumericPAeqTerm

