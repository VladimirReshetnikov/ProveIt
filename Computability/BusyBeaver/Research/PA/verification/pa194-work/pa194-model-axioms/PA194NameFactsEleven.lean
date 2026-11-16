import PA194NameVariableFull
import PA194NameRefl
import PA194NameOfUniq
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
structure NameFactsRemainingEleven : Prop where
  atomTransfer : ∀ s₁ s₁' s₂ s₂' : V, IsSemiterm PA194PAeq.language 0 s₁ →
    IsSemiterm PA194PAeq.language 0 s₁' → IsSemiterm PA194PAeq.language 0 s₂ →
    IsSemiterm PA194PAeq.language 0 s₂' →
    GDerivable T (insert (neg SourceL (tr (nameAll s₁ s₁')))
      (insert (neg SourceL (tr (nameAll s₂ s₂')))
        (insert (neg SourceL (tr (peq s₁ s₂))) (insert (tr (peq s₁' s₂')) (∅ : V)))))
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

theorem nameFacts_of_eleven_fields (R : NameFactsRemainingEleven (V := V) T)
    (huv : ∀ i : V, GDerivable T (insert (tr (uniq (^&i))) (∅ : V)))
    (huz : GDerivable T (insert (tr (uniq (zeroT : V))) (∅ : V)))
    (hev : ∀ i : V, GDerivable T (insert (tr (exName (^&i))) (∅ : V)))
    (hez : GDerivable T (insert (tr (exName (zeroT : V))) (∅ : V))) : NameFacts (V := V) T := by
  exact ⟨(fun s hs => nRefl s hs), R.atomTransfer, (fun t c ht => nameOfUniq ht c), R.nameOfEq,
    R.nSucc, R.nAdd, R.nMul, huv, huz, R.uSucc, R.uAdd, R.uMul, hev, hez, R.eSucc, R.eAdd, R.eMul⟩

#print axioms nameFacts_of_eleven_fields
end generic
end PA194GuardedCompiler
