import PA194NameVariableFull
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (T : Theory SourceL) [T.Δ₁]
structure NameFactsWithoutBaseExistence : Prop where
  nRefl : ∀ s : V, IsSemiterm PA194PAeq.language 0 s →
    GDerivable T (insert (tr (nameAll s s)) (∅ : V))
  /-- If names transfer from `s₁` to `s₁'` and from `s₂` to `s₂'`, so does equality. -/
  atomTransfer : ∀ s₁ s₁' s₂ s₂' : V, IsSemiterm PA194PAeq.language 0 s₁ →
    IsSemiterm PA194PAeq.language 0 s₁' → IsSemiterm PA194PAeq.language 0 s₂ →
    IsSemiterm PA194PAeq.language 0 s₂' →
    GDerivable T (insert (neg SourceL (tr (nameAll s₁ s₁')))
      (insert (neg SourceL (tr (nameAll s₂ s₂')))
        (insert (neg SourceL (tr (peq s₁ s₂))) (insert (tr (peq s₁' s₂')) (∅ : V)))))
  nameOfUniq : ∀ t c : V, IsSemiterm PA194PAeq.language 0 t →
    GDerivable T (insert (neg SourceL (tr (uniq t)))
      (insert (neg SourceL (tr (peq (^&c) t))) (insert (tr (nameAll t (^&c))) (∅ : V))))
  nameOfEq : ∀ t c : V, IsSemiterm PA194PAeq.language 0 t →
    GDerivable T (insert (neg SourceL (tr (peq (^&c) t)))
      (insert (tr (nameAll (^&c) t)) (∅ : V)))
  nSucc : ∀ s s' : V, IsSemiterm PA194PAeq.language 0 s → IsSemiterm PA194PAeq.language 0 s' →
    GDerivable T (insert (neg SourceL (tr (nameAll s s')))
      (insert (tr (nameAll (succT s) (succT s'))) (∅ : V)))
  nAdd : ∀ s₁ s₁' s₂ s₂' : V, IsSemiterm PA194PAeq.language 0 s₁ →
    IsSemiterm PA194PAeq.language 0 s₁' → IsSemiterm PA194PAeq.language 0 s₂ →
    IsSemiterm PA194PAeq.language 0 s₂' →
    GDerivable T (insert (neg SourceL (tr (nameAll s₁ s₁')))
      (insert (neg SourceL (tr (nameAll s₂ s₂')))
        (insert (tr (nameAll (addT s₁ s₂) (addT s₁' s₂'))) (∅ : V))))
  nMul : ∀ s₁ s₁' s₂ s₂' : V, IsSemiterm PA194PAeq.language 0 s₁ →
    IsSemiterm PA194PAeq.language 0 s₁' → IsSemiterm PA194PAeq.language 0 s₂ →
    IsSemiterm PA194PAeq.language 0 s₂' →
    GDerivable T (insert (neg SourceL (tr (nameAll s₁ s₁')))
      (insert (neg SourceL (tr (nameAll s₂ s₂')))
        (insert (tr (nameAll (mulT s₁ s₂) (mulT s₁' s₂'))) (∅ : V))))
  uVar : ∀ i : V, GDerivable T (insert (tr (uniq (^&i))) (∅ : V))
  uZero : GDerivable T (insert (tr (uniq (zeroT : V))) (∅ : V))
  uSucc : ∀ s : V, IsSemiterm PA194PAeq.language 0 s →
    GDerivable T (insert (neg SourceL (tr (uniq s))) (insert (tr (uniq (succT s))) (∅ : V)))
  uAdd : ∀ s s' : V, IsSemiterm PA194PAeq.language 0 s → IsSemiterm PA194PAeq.language 0 s' →
    GDerivable T (insert (neg SourceL (tr (uniq s))) (insert (neg SourceL (tr (uniq s')))
      (insert (tr (uniq (addT s s'))) (∅ : V))))
  uMul : ∀ s s' : V, IsSemiterm PA194PAeq.language 0 s → IsSemiterm PA194PAeq.language 0 s' →
    GDerivable T (insert (neg SourceL (tr (uniq s))) (insert (neg SourceL (tr (uniq s')))
      (insert (tr (uniq (mulT s s'))) (∅ : V))))
  eSucc : ∀ s : V, IsSemiterm PA194PAeq.language 0 s →
    GDerivable T (insert (neg SourceL (tr (exName s))) (insert (tr (exName (succT s))) (∅ : V)))
  eAdd : ∀ s s' : V, IsSemiterm PA194PAeq.language 0 s → IsSemiterm PA194PAeq.language 0 s' →
    GDerivable T (insert (neg SourceL (tr (exName s))) (insert (neg SourceL (tr (exName s')))
      (insert (tr (exName (addT s s'))) (∅ : V))))
  eMul : ∀ s s' : V, IsSemiterm PA194PAeq.language 0 s → IsSemiterm PA194PAeq.language 0 s' →
    GDerivable T (insert (neg SourceL (tr (exName s))) (insert (neg SourceL (tr (exName s')))
      (insert (tr (exName (mulT s s'))) (∅ : V))))

theorem nameFacts_of_other_fields (R : NameFactsWithoutBaseExistence (V := V) T)
    (hv : ∀ i : V, GDerivable T (insert (tr (exName (^&i))) (∅ : V)))
    (hz : GDerivable T (insert (tr (exName (zeroT : V))) (∅ : V))) : NameFacts (V := V) T := by
  exact ⟨R.nRefl, R.atomTransfer, R.nameOfUniq, R.nameOfEq, R.nSucc, R.nAdd, R.nMul, R.uVar, R.uZero, R.uSucc, R.uAdd, R.uMul, hv, hz, R.eSucc, R.eAdd, R.eMul⟩

#print axioms nameFacts_of_other_fields
end generic
end PA194GuardedCompiler
