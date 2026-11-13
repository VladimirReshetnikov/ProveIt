module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueClosedEnvironment
@[expose] public section

/-! Actual bound substitution in value syntax with context-zero target term
environments. Source arithmetic syntax stays unchanged. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalPredicateTemplate (substTerms substTerms_length substTerms_nth)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem targetTerm_subst_zero {t:V} (w:V) (h:IsSemiterm language 0 t) :
    termSubst language w t=t := by
  rcases (RelationalSource.source_term_cases 0 t).mp h with ⟨i,hi,rfl⟩|⟨i,rfl⟩
  · exact False.elim (by simpa using hi)
  · simp

theorem substTerms_zero_arity {k v:V} (w:V) (h:IsSemitermVec language k 0 v) :
    substTerms w v=v := by
  apply nth_ext' k (substTerms_length h) h.lh
  intro i hi
  rw [substTerms_nth h hi,targetTerm_subst_zero w (h.nth hi)]

theorem valueSyntax_bound_instance {s b f t n x : V}
    (hb:IsSemitermVec language s 0 b) (hf:IsSemitermVec language (len f) 0 f)
    (ht:IsSemiterm Presentation.language s t) (hbound:t≤len f)
    (hx:IsSemiterm language n x) :
    substs1 language x (valueSyntax (parameters b f (qqBvar 0)) t)=
      valueSyntax (parameters b f x) t := by
  have hb1 : IsSemitermVec language s 1 b := by
    rw [←shiftTerms_zero_arity hb]
    simpa using shiftTerms_isSemitermVec hb
  have hf1 : IsSemitermVec language (len f) 1 f := by
    rw [←shiftTerms_zero_arity hf]
    simpa only [shiftTerms_length hf,zero_add] using shiftTerms_isSemitermVec hf
  have h : TermCovered s 1 (parameters b f (qqBvar 0)) t := by
    refine ⟨?_,ht,?_⟩
    · simpa [ParametersValid] using And.intro hb1 (And.intro hf1 (show IsSemiterm language 1 (qqBvar 0) by simp))
    · simpa using hbound
  have hw : IsSemitermVec language 1 n (x∷0) := IsSemitermVec.singleton.mpr hx
  change subst language (x∷0) _=_
  rw [valueSyntax_targetSubst h hw]
  simp [targetSubstParameters,substTerms_zero_arity _ hb,substTerms_zero_arity _ hf]

#print axioms targetTerm_subst_zero
#print axioms substTerms_zero_arity
#print axioms valueSyntax_bound_instance
end M6.PA.NumericPAeqTerm

