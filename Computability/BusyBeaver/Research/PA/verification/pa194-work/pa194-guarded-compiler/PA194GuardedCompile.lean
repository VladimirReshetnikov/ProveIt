import PA194ConditionalRefutation
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Domain guards

The translation of `pa194-model-logic` sends a free variable of the arithmetic language to a
term of the relational source language, and a quantifier to a quantifier relativized to the
ordinal domain. A derivable arithmetic sequent with free variables is then translated to a
sequent that the source theory proves only under the hypotheses that the images of the free
variables lie in the domain. This module defines the guards `¬ Dom(&i)` that carry those
hypotheses, and removes them from a refutation.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher
open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The guard of one free variable -/

/-- The guard of the source free variable `i`: the negated domain formula `¬ Dom(&i)`. -/
noncomputable def guard (i : V) : V := neg SourceL (domainCode (^&i))
noncomputable def guardGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out i. ∃ x d, !qqFvarDef x i ∧ !(templateOneGraph domainTemplate) d x ∧ !(negGraph SourceL) out d”
theorem guard_graph (out i : V) : guardGraph.val.Evalb ![out,i] ↔ out = guard i := by
  simp [guardGraph,guard,domainCode,Matrix.comp_vecCons'']
instance guard_defined : 𝚺₁-Function₁ (guard : V → V) via guardGraph := .mk fun v => by
  change guardGraph.val.Evalb v ↔ v 0 = guard (v 1)
  have hv : ![v 0,v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  simpa only [hv] using guard_graph (v 0) (v 1)
instance guard_definable : 𝚺₁-Function₁ (guard : V → V) := guard_defined.to_definable

theorem guard_valid (i : V) : IsFormula SourceL (guard i) := by
  have h : IsSemiformula SourceL 0 (domainCode (^&i : V)) := domainCode_valid (by simp)
  exact IsSemiformula.neg_iff.mpr h

/-- The quoted domain template has no free variable. -/
theorem domainTemplate_shift : Rewriting.shift domainTemplate = domainTemplate := by
  simp [domainTemplate, Rewriting.shift, app_eq_rewAux, domain_rew]
theorem domainTemplate_quote_shift :
    shift SourceL (⌜domainTemplate⌝ : V) = ⌜domainTemplate⌝ := by
  rw [← Semiformula.quote_shift, domainTemplate_shift]
theorem domainTemplate_quote_valid : IsSemiformula SourceL 1 (⌜domainTemplate⌝ : V) := by
  simp

/-- Shifting a domain instance shifts its term. -/
theorem domainCode_shift {n z : V} (hz : IsSemiterm SourceL n z) :
    shift SourceL (domainCode z) = domainCode (termShift SourceL z) := by
  have hw : IsSemitermVec SourceL 1 n (?[z] : V) := by simp [hz]
  show shift SourceL (subst SourceL (?[z] : V) ⌜domainTemplate⌝) =
    subst SourceL (?[termShift SourceL z] : V) ⌜domainTemplate⌝
  rw [shift_substs domainTemplate_quote_valid hw, domainTemplate_quote_shift,
    termShiftVec_cons₁ hz.isUTerm]

theorem guard_shift (i : V) : shift SourceL (guard i) = guard (i+1) := by
  have hd : IsSemiformula SourceL 0 (domainCode (^&i : V)) := domainCode_valid (by simp)
  unfold guard
  rw [shift_neg hd, domainCode_shift (n := 0) (by simp), termShift_fvar]

/-- The body `¬ Dom(#0)`; its instance at the free variable `0` is `guard 0`. -/
noncomputable def guardBody : V := neg SourceL (domainCode (^#(0 : V)))
theorem domainBody_valid : IsSemiformula SourceL 1 (domainCode (^#(0 : V))) :=
  domainCode_valid (by simp)
theorem guardBody_valid : IsSemiformula SourceL 1 (guardBody : V) :=
  IsSemiformula.neg_iff.mpr domainBody_valid
theorem free_guardBody : free SourceL (guardBody : V) = guard 0 := by
  have hw : IsSemitermVec SourceL 1 0 (?[^&(0 : V)] : V) := by simp
  have hv : IsSemitermVec SourceL 1 1 (?[^#(0 : V)] : V) := by simp
  show subst SourceL (?[^&(0 : V)] : V) (shift SourceL (neg SourceL (domainCode (^#(0 : V))))) =
    neg SourceL (domainCode (^&(0 : V)))
  rw [shift_neg domainBody_valid, domainCode_shift (n := 1) (by simp), termShift_bvar,
    substs_neg domainBody_valid hw]
  congr 1
  show subst SourceL (?[^&(0 : V)] : V) (subst SourceL (?[^#(0 : V)] : V) ⌜domainTemplate⌝) =
    subst SourceL (?[^&(0 : V)] : V) ⌜domainTemplate⌝
  rw [substs_substs domainTemplate_quote_valid hw hv, termSubstVec_cons₁ (by simp), termSubst_bvar]
  simp
theorem neg_all_guardBody :
    neg SourceL (^∀ (guardBody : V)) = ^∃ (domainCode (^#(0 : V))) := by
  rw [neg_all guardBody_valid.isUFormula]
  unfold guardBody
  rw [IsUFormula.neg_neg domainBody_valid.isUFormula]

/-! ### Guard sets -/

/-- The guards of the free variables below `n`. -/
noncomputable def guards (n : V) : V := hfsImage guard (under n)
theorem mem_guards {n q : V} : q ∈ guards n ↔ ∃ i < n, q = guard i := by
  simp [guards, mem_hfsImage_iff]
instance guards_definable : 𝚺₁-Function₁ (guards : V → V) := by
  haveI : 𝚺₁-Function₁ (hfsImage (guard : V → V)) := hfsImage.definable guard guardGraph
  show 𝚺₁-Function₁ (fun n : V => hfsImage guard (under n))
  definability
theorem guards_valid (n : V) : IsFormulaSet SourceL (guards n) := by
  intro q hq
  obtain ⟨i,_,rfl⟩ := mem_guards.mp hq
  exact guard_valid i
theorem guards_mono {n m : V} (h : n ≤ m) : guards n ⊆ guards m := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := mem_guards.mp hq
  exact mem_guards.mpr ⟨i,lt_of_lt_of_le hi h,rfl⟩
theorem guards_zero : guards (0 : V) = ∅ := by
  apply mem_ext
  intro q
  simp [mem_guards]
/-- Every guard below `n+1` is `guard 0` or the shift of a guard below `n`. -/
theorem guards_succ_subset (n : V) :
    guards (n+1) ⊆ insert (guard 0) (setShift SourceL (guards n)) := by
  intro q hq
  obtain ⟨j,hj,rfl⟩ := mem_guards.mp hq
  rcases zero_or_succ j with (rfl | ⟨i,rfl⟩)
  · exact mem_bitInsert_iff.mpr (Or.inl rfl)
  · refine mem_bitInsert_iff.mpr (Or.inr ?_)
    exact mem_setShift_iff.mpr ⟨guard i,mem_guards.mpr ⟨i,by simpa using hj,rfl⟩,(guard_shift i).symm⟩
/-- The shift of a guard set is a set of guards one index higher. -/
theorem setShift_guards_subset (n : V) : setShift SourceL (guards n) ⊆ guards (n+1) := by
  intro q hq
  obtain ⟨p,hp,rfl⟩ := mem_setShift_iff.mp hq
  obtain ⟨i,hi,rfl⟩ := mem_guards.mp hp
  exact mem_guards.mpr ⟨i+1,by simpa using hi,guard_shift i⟩

variable (T : Theory SourceL) [T.Δ₁]

/-! ### Removing the guards at the root -/

/-- One guard is removed by generalizing it and cutting against `∃x Dom(x)`. -/
theorem discharge_step (hdom : Provable T (^∃ (domainCode (^#(0 : V))))) (m : V)
    (h : Derivable T (guards (m+1) ∪ {(^⊥ : V)})) : Derivable T (guards m ∪ {(^⊥ : V)}) := by
  have hΓ : IsFormulaSet SourceL (guards m ∪ {(^⊥ : V)}) :=
    IsFormulaSet.union.mpr ⟨guards_valid m,by simp⟩
  have hsub : guards (m+1) ∪ {(^⊥ : V)} ⊆
      insert (free SourceL guardBody) (setShift SourceL (guards m ∪ {(^⊥ : V)})) := by
    intro q hq
    rw [free_guardBody, mem_setShift_union]
    rcases mem_cup_iff.mp hq with hq | hq
    · rcases mem_bitInsert_iff.mp (guards_succ_subset m hq) with h0 | hs
      · exact mem_bitInsert_iff.mpr (Or.inl h0)
      · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inl hs)))
    · have hq' : q = ^⊥ := by simpa using hq
      subst hq'
      refine mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inr ?_)))
      exact mem_setShift_iff.mpr ⟨^⊥,by simp,by simp⟩
  have h1 : Derivable T (insert (free SourceL guardBody) (setShift SourceL (guards m ∪ {(^⊥ : V)}))) :=
    Derivable.wk (IsFormulaSet.insert_iff.mpr ⟨guardBody_valid.free,hΓ.setShift⟩) hsub h
  have h2 : Derivable T (insert (^∀ guardBody) (guards m ∪ {(^⊥ : V)})) :=
    Derivable.all guardBody_valid h1
  have hex : IsFormula SourceL (^∃ (domainCode (^#(0 : V)))) := by
    simpa using (domainBody_valid (V := V))
  have h3 : Derivable T (insert (neg SourceL (^∀ guardBody)) (guards m ∪ {(^⊥ : V)})) := by
    rw [neg_all_guardBody]
    exact Derivable.wk (IsFormulaSet.insert_iff.mpr ⟨hex,hΓ⟩)
      (insert_subset_insert_of_subset _ (empty_subset _)) hdom.toDerivable
  exact Derivable.cut (^∀ guardBody) h2 h3

/-- All guards are removed when the source theory proves that the domain is inhabited. -/
theorem discharge_guards (hdom : Provable T (^∃ (domainCode (^#(0 : V))))) (n : V)
    (h : Derivable T (guards n ∪ {(^⊥ : V)})) : Provable T (^⊥ : V) := by
  have hstep : ∀ k ≤ n, ∃ m, m + k = n ∧ Derivable T (guards m ∪ {(^⊥ : V)}) := by
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
      · exact ⟨m',by rw [← hm, add_assoc, add_comm k 1],discharge_step T hdom m' hder⟩
  obtain ⟨m,hm,hder⟩ := hstep n le_rfl
  have hm0 : m = 0 := by simpa using hm
  subst hm0
  rw [guards_zero, union_empty_eq_left] at hder
  apply Derivable.toProvable
  rw [← singleton_eq_insert]
  exact hder

#print axioms guard_graph
#print axioms guard_shift
#print axioms free_guardBody
#print axioms guards_succ_subset
#print axioms discharge_guards
end generic
end PA194GuardedCompiler
