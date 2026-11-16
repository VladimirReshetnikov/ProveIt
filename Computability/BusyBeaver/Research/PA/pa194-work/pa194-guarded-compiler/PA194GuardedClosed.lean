import PA194FixedAxiomQuotes
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Guards are discharged at every formula without free variables

`discharge_guards` of `PA194GuardedCompile` removes the domain guards at `⊥`. The same
argument works for any formula that is not changed by the shift of free variables:
`gd_provable_of_shift`. For the translation of an arithmetic formula invariant
under shift, a guarded derivation is therefore a proof (`tr_provable_of_closed`), and the
four axioms of `PA194FixedAxiomQuotes` are proved outright once the domain is inhabited.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher PA194Schematic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (T : Theory SourceL) [T.Δ₁]

/-- One guard is removed in front of a formula invariant under shift. -/
theorem discharge_step_of_shift (hdom : Provable T (^∃ (domainCode (^#(0 : V))))) {φ : V}
    (hφ : IsFormula SourceL φ) (hs : shift SourceL φ = φ) (m : V)
    (h : Derivable T (guards (m+1) ∪ {φ})) : Derivable T (guards m ∪ {φ}) := by
  have hΓ : IsFormulaSet SourceL (guards m ∪ {φ}) :=
    IsFormulaSet.union.mpr ⟨guards_valid m,by simpa using hφ⟩
  have hsub : guards (m+1) ∪ {φ} ⊆
      insert (free SourceL guardBody) (setShift SourceL (guards m ∪ {φ})) := by
    intro q hq
    rw [free_guardBody, mem_setShift_union]
    rcases mem_cup_iff.mp hq with hq | hq
    · rcases mem_bitInsert_iff.mp (guards_succ_subset m hq) with h0 | hs'
      · exact mem_bitInsert_iff.mpr (Or.inl h0)
      · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inl hs')))
    · have hq' : q = φ := by simpa using hq
      subst hq'
      refine mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inr ?_)))
      exact mem_setShift_iff.mpr ⟨q,by simp,hs.symm⟩
  have h1 : Derivable T (insert (free SourceL guardBody) (setShift SourceL (guards m ∪ {φ}))) :=
    Derivable.wk (IsFormulaSet.insert_iff.mpr ⟨guardBody_valid.free,hΓ.setShift⟩) hsub h
  have h2 : Derivable T (insert (^∀ guardBody) (guards m ∪ {φ})) :=
    Derivable.all guardBody_valid h1
  have hex : IsFormula SourceL (^∃ (domainCode (^#(0 : V)))) := by
    simpa using (domainBody_valid (V := V))
  have h3 : Derivable T (insert (neg SourceL (^∀ guardBody)) (guards m ∪ {φ})) := by
    rw [neg_all_guardBody]
    exact Derivable.wk (IsFormulaSet.insert_iff.mpr ⟨hex,hΓ⟩)
      (insert_subset_insert_of_subset _ (empty_subset _)) hdom.toDerivable
  exact Derivable.cut (^∀ guardBody) h2 h3

variable {T}

/-- A guarded derivation of a formula invariant under shift is a proof, when the source
theory proves that the domain is inhabited. -/
theorem gd_provable_of_shift (hdom : Provable T (^∃ (domainCode (^#(0 : V))))) {φ : V}
    (hφ : IsFormula SourceL φ) (hs : shift SourceL φ = φ)
    (h : GDerivable T (insert φ (∅ : V))) : Provable T φ := by
  obtain ⟨n, h⟩ := h
  rw [← singleton_eq_insert] at h
  have hstep : ∀ k ≤ n, ∃ m, m + k = n ∧ Derivable T (guards m ∪ {φ}) := by
    intro k hk
    induction k using ISigma1.sigma1_succ_induction
    · definability
    case zero => exact ⟨n,by simp,h⟩
    case succ k ih =>
      obtain ⟨m,hm,hder⟩ := ih (le_trans (by simp) hk)
      rcases zero_or_succ m with (rfl | ⟨m',rfl⟩)
      · have hkn : k = n := by simpa using hm
        subst hkn
        exact absurd hk (not_le.mpr (lt_add_one k))
      · exact ⟨m',by rw [← hm, add_assoc, add_comm k 1],
          discharge_step_of_shift T hdom hφ hs m' hder⟩
  obtain ⟨m,hm,hder⟩ := hstep n le_rfl
  have hm0 : m = 0 := by simpa using hm
  subst hm0
  rw [guards_zero, union_empty_eq_left] at hder
  apply Derivable.toProvable
  rw [← singleton_eq_insert]
  exact hder

/-- For an arithmetic formula invariant under shift, a guarded derivation of its translation
is a proof of it. -/
theorem tr_provable_of_closed (hdom : Provable T (^∃ (domainCode (^#(0 : V))))) {φ : V}
    (hφ : IsSemiformula PA194PAeq.language 0 φ) (hs : shift PA194PAeq.language φ = φ)
    (h : GDerivable T (insert (tr φ) (∅ : V))) : Provable T (tr φ) :=
  gd_provable_of_shift hdom (tr_valid hφ) (by rw [← tr_shift hφ, hs]) h

/-- The quote of a standard proposition that is not changed by the standard shift. -/
theorem quote_shift_fixed' {σ : Proposition PA194PAeq.language} (h : σ.freeVariables = ∅) :
    shift PA194PAeq.language (⌜σ⌝ : V) = ⌜σ⌝ := by
  have hs : Rewriting.shift σ = σ :=
    FirstOrder.Semiformula.rew_eq_self_of (fun x => x.elim0)
      (fun x hx => absurd hx (by simp [FirstOrder.Semiformula.FVar?, h]))
  rw [← Semiformula.quote_shift, hs]

section axioms
variable (S : SourceFacts (V := V) T) (hdom : Provable T (^∃ (domainCode (^#(0 : V)))))
include S hdom

theorem addCongruence_provable : Provable T (tr (⌜PA194PAeq.addCongruence⌝ : V)) :=
  tr_provable_of_closed hdom (by simp) (quote_shift_fixed' (σ := PA194PAeq.addCongruence) (by decide)) (addCongruence_tr S)
theorem mulCongruence_provable : Provable T (tr (⌜PA194PAeq.mulCongruence⌝ : V)) :=
  tr_provable_of_closed hdom (by simp) (quote_shift_fixed' (σ := PA194PAeq.mulCongruence) (by decide)) (mulCongruence_tr S)
theorem addSucc_provable
    (hA3 : T.internalize V ⊢ (tHyp sA3 : Bootstrapping.Semiformula V SourceL 0)) :
    Provable T (tr (⌜PA194PAeq.addSucc⌝ : V)) :=
  tr_provable_of_closed hdom (by simp) (quote_shift_fixed' (σ := PA194PAeq.addSucc) (by decide)) (addSucc_tr S hA3)
theorem mulSucc_provable
    (hM3 : T.internalize V ⊢ (tHyp sM3 : Bootstrapping.Semiformula V SourceL 0)) :
    Provable T (tr (⌜PA194PAeq.mulSucc⌝ : V)) :=
  tr_provable_of_closed hdom (by simp) (quote_shift_fixed' (σ := PA194PAeq.mulSucc) (by decide)) (mulSucc_tr S hM3)

end axioms

#print axioms gd_provable_of_shift
#print axioms tr_provable_of_closed
#print axioms addCongruence_provable
#print axioms mulCongruence_provable
#print axioms addSucc_provable
#print axioms mulSucc_provable
end generic
end PA194GuardedCompiler
