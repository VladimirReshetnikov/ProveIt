import PA194ConditionalRefutation
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# A compiler invariant with domain guards

The translation of `pa194-model-logic` sends a free variable of the arithmetic language to a
term of the relational source language, and a quantifier to a quantifier relativized to the
ordinal domain. A derivable arithmetic sequent with free variables is then translated to a
sequent that the source theory proves only under the hypotheses that the images of the free
variables lie in the domain. The invariant of this module therefore carries a set of guards
`¬ Dom(&i)` next to the translated sequent. The propositional and structural rules are proved
for it here, and the guards are removed at the root of a refutation.
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

/-! ### The guarded invariant -/

variable (U : Theory PA194PAeq.language) [U.Δ₁] (T : Theory SourceL) [T.Δ₁]

/-- The source theory derives the translated sequent together with the guards below `n`. -/
def Guarded (param n s : V) : Prop := Derivable T (guards n ∪ translatedSequent param s)

theorem Guarded.mono {param n m s : V}
    (hs : IsFormulaSet SourceL (translatedSequent param s)) (h : Guarded T param n s) (hnm : n ≤ m) :
    Guarded T param m s := by
  refine Derivable.wk (IsFormulaSet.union.mpr ⟨guards_valid m,hs⟩) ?_ h
  intro q hq
  rcases mem_cup_iff.mp hq with hq | hq
  · exact mem_cup_iff.mpr (Or.inl (guards_mono hnm hq))
  · exact mem_cup_iff.mpr (Or.inr hq)

/-- The four rules that are not proved here, in the guarded form. -/
structure GuardedRules (param : V) : Prop where
  allRule : ∀ s p d, IsFormulaSet PA194PAeq.language s → ^∀ p ∈ s →
    DerivationOf U d (insert (free PA194PAeq.language p) (setShift PA194PAeq.language s)) →
    allIntro s p d < len (nth param 1) →
    Guarded T param d (fstIdx d) → Guarded T param (allIntro s p d) s
  exsRule : ∀ s p t d, IsFormulaSet PA194PAeq.language s → ^∃ p ∈ s → IsTerm PA194PAeq.language t →
    DerivationOf U d (insert (substs1 PA194PAeq.language t p) s) →
    exsIntro s p t d < len (nth param 1) →
    Guarded T param d (fstIdx d) → Guarded T param (exsIntro s p t d) s
  shiftRule : ∀ s d, IsFormulaSet PA194PAeq.language s → s = setShift PA194PAeq.language (fstIdx d) →
    Derivation U d → shiftRule s d < len (nth param 1) →
    Guarded T param d (fstIdx d) → Guarded T param (shiftRule s d) s
  theoryAxiom : ∀ s p, IsFormulaSet PA194PAeq.language s → p ∈ s → p ∈ U.Δ₁Class →
    axm s p < len (nth param 1) → Guarded T param (axm s p) s

theorem lift_insert {param n m p s : V} (hnm : n ≤ m) :
    guards n ∪ translatedSequent param (insert p s) ⊆
      insert (translateFormula param p) (guards m ∪ translatedSequent param s) := by
  intro x hx
  rw [translatedSequent_insert] at hx
  rcases mem_cup_iff.mp hx with h | h
  · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inl (guards_mono hnm h))))
  · rcases mem_bitInsert_iff.mp h with h | h
    · exact mem_bitInsert_iff.mpr (Or.inl h)
    · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inr h)))

/-- A guarded premise with one more formula, moved under the guards of a later index. -/
theorem Guarded.lift {param n m p s : V} (hnm : n ≤ m)
    (hp : IsFormula SourceL (translateFormula param p))
    (hs : IsFormulaSet SourceL (translatedSequent param s))
    (h : Guarded T param n (insert p s)) :
    Derivable T (insert (translateFormula param p) (guards m ∪ translatedSequent param s)) :=
  Derivable.wk (IsFormulaSet.insert_iff.mpr ⟨hp,IsFormulaSet.union.mpr ⟨guards_valid m,hs⟩⟩)
    (lift_insert hnm) h

/-- The compiler for the rules that need no supplier, with the invariant `Guarded`. -/
theorem guarded_compile {param d : V} (hparam : ParametersValid 0 0 param)
    (S : GuardedRules U T param) (hd : Derivation U d) (hbound : d < len (nth param 1)) :
    Guarded T param d (fstIdx d) := by
  let P : V → Prop := fun d => d < len (nth param 1) →
    Derivable T (guards d ∪ translatedSequent param (fstIdx d))
  have hP : 𝚺₁-Predicate P := by
    haveI : 𝚺₁-Function₂ (translatedSequent : V → V → V) := translatedSequent_defined.to_definable
    dsimp [P]
    definability
  have scope : ∀ {q : V}, IsSemiformula PA194PAeq.language 0 q → q < len (nth param 1) →
      IsFormula SourceL (translateFormula param q) := fun hq hlen =>
    formula_scope_translate hq.isUFormula 0 0 param hq hparam hlen
  have hcompile : P d := by
    apply Derivation.induction1 𝚺 hP hd
    · intro s hs p hp hnp hsize
      rw [fstIdx_axL]
      have hlen : ∀ q ∈ s, q < len (nth param 1) := seqMembers_bounded (lt_trans (seq_lt_axL s p) hsize)
      have hvalid := translatedSequent_valid hparam hs hlen
      have heq := translateFormula_neg (hs p hp).isUFormula 0 0 param (hs p hp) hparam (hlen p hp) (hlen _ hnp)
      refine Derivable.em (IsFormulaSet.union.mpr ⟨guards_valid _,hvalid⟩) (translateFormula param p) ?_ ?_
      · exact mem_cup_iff.mpr (Or.inr (translatedSequent_mem.mpr ⟨p,hp,rfl⟩))
      · exact mem_cup_iff.mpr (Or.inr (translatedSequent_mem.mpr ⟨_,hnp,heq.symm⟩))
    · intro s hs hp hsize
      rw [fstIdx_verumIntro]
      have hlen : ∀ q ∈ s, q < len (nth param 1) := seqMembers_bounded (lt_trans (seq_lt_verumIntro s) hsize)
      have hvalid := translatedSequent_valid hparam hs hlen
      refine Derivable.verum (IsFormulaSet.union.mpr ⟨guards_valid _,hvalid⟩) ?_
      exact mem_cup_iff.mpr (Or.inr (translatedSequent_mem.mpr ⟨_,hp,(translate_verum param).symm⟩))
    · intro s hs p q dp dq hpq hdp hdq ihp ihq hsize
      rw [fstIdx_andIntro]
      have hlen : ∀ r ∈ s, r < len (nth param 1) :=
        seqMembers_bounded (lt_trans (seq_lt_andIntro s p q dp dq) hsize)
      have hvalid := translatedSequent_valid hparam hs hlen
      have hpqf := IsSemiformula.and.mp (hs _ hpq)
      have hp' := ihp (lt_trans (dp_lt_andIntro s p q dp dq) hsize)
      have hq' := ihq (lt_trans (dq_lt_andIntro s p q dp dq) hsize)
      rw [hdp.1] at hp'
      rw [hdq.1] at hq'
      have hmem : translateFormula param p ^⋏ translateFormula param q ∈
          guards (andIntro s p q dp dq) ∪ translatedSequent param s :=
        mem_cup_iff.mpr (Or.inr (translatedSequent_mem.mpr
          ⟨_,hpq,(translate_and param p q hpqf.1.isUFormula hpqf.2.isUFormula).symm⟩))
      exact Derivable.and_m hmem
        (Guarded.lift T (le_of_lt (dp_lt_andIntro s p q dp dq))
          (scope hpqf.1 (lt_trans (p_lt_andIntro s p q dp dq) hsize)) hvalid hp')
        (Guarded.lift T (le_of_lt (dq_lt_andIntro s p q dp dq))
          (scope hpqf.2 (lt_trans (q_lt_andIntro s p q dp dq) hsize)) hvalid hq')
    · intro s hs p q dp hpq hdp ih hsize
      rw [fstIdx_orIntro]
      have hlen : ∀ r ∈ s, r < len (nth param 1) :=
        seqMembers_bounded (lt_trans (seq_lt_orIntro s p q dp) hsize)
      have hvalid := translatedSequent_valid hparam hs hlen
      have hpqf := IsSemiformula.or.mp (hs _ hpq)
      have hp' := ih (lt_trans (d_lt_orIntro s p q dp) hsize)
      rw [hdp.1] at hp'
      have hpscope := scope hpqf.1 (lt_trans (p_lt_orIntro s p q dp) hsize)
      have hqscope := scope hpqf.2 (lt_trans (q_lt_orIntro s p q dp) hsize)
      have hmem : translateFormula param p ^⋎ translateFormula param q ∈
          guards (orIntro s p q dp) ∪ translatedSequent param s :=
        mem_cup_iff.mpr (Or.inr (translatedSequent_mem.mpr
          ⟨_,hpq,(translate_or param p q hpqf.1.isUFormula hpqf.2.isUFormula).symm⟩))
      refine Derivable.or_m hmem ?_
      refine Derivable.wk (IsFormulaSet.insert_iff.mpr ⟨hpscope,IsFormulaSet.insert_iff.mpr
        ⟨hqscope,IsFormulaSet.union.mpr ⟨guards_valid _,hvalid⟩⟩⟩) ?_ hp'
      intro x hx
      rw [translatedSequent_insert,translatedSequent_insert] at hx
      rcases mem_cup_iff.mp hx with h | h
      · exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr
          (Or.inl (guards_mono (le_of_lt (d_lt_orIntro s p q dp)) h))))))
      · rcases mem_bitInsert_iff.mp h with h | h
        · exact mem_bitInsert_iff.mpr (Or.inl h)
        · rcases mem_bitInsert_iff.mp h with h | h
          · exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inl h)))
          · exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inr h)))))
    · intro s hs p dp hp hdp ih hsize
      rw [fstIdx_allIntro]
      exact S.allRule s p dp hs hp hdp hsize (ih (lt_trans (s_lt_allIntro s p dp) hsize))
    · intro s hs p t dp hp ht hdp ih hsize
      rw [fstIdx_exsIntro]
      exact S.exsRule s p t dp hs hp ht hdp hsize (ih (lt_trans (d_lt_exsIntro s p t dp) hsize))
    · intro s hs dp hsub hdp ih hsize
      rw [fstIdx_wkRule]
      have hlen : ∀ q ∈ s, q < len (nth param 1) := seqMembers_bounded (lt_trans (seq_lt_wkRule s dp) hsize)
      have hvalid := translatedSequent_valid hparam hs hlen
      have h' := ih (lt_trans (d_lt_wkRule s dp) hsize)
      refine Derivable.wk (IsFormulaSet.union.mpr ⟨guards_valid _,hvalid⟩) ?_ h'
      intro x hx
      rcases mem_cup_iff.mp hx with h | h
      · exact mem_cup_iff.mpr (Or.inl (guards_mono (le_of_lt (d_lt_wkRule s dp)) h))
      · exact mem_cup_iff.mpr (Or.inr (translatedSequent_subset hsub h))
    · intro s hs dp heq hdp ih hsize
      rw [fstIdx_shiftRule]
      exact S.shiftRule s dp hs heq hdp hsize (ih (lt_trans (d_lt_shiftRule s dp) hsize))
    · intro s hs p dp dq hdp hdq ihp ihq hsize
      rw [fstIdx_cutRule]
      have hlen : ∀ r ∈ s, r < len (nth param 1) :=
        seqMembers_bounded (lt_trans (seq_lt_cutRule s p dp dq) hsize)
      have hvalid := translatedSequent_valid hparam hs hlen
      have hn_mem : neg PA194PAeq.language p ∈ fstIdx dq := by rw [hdq.1]; simp
      have hp_scope : IsSemiformula PA194PAeq.language 0 p := hdp.isFormulaSet p (by simp)
      have hp_len : p < len (nth param 1) := lt_trans (p_lt_cutRule s p dp dq) hsize
      have hn_lt : neg PA194PAeq.language p < dq := lt_of_lt_of_le (lt_of_mem hn_mem) (fstIdx_le_self dq)
      have hn_len : neg PA194PAeq.language p < len (nth param 1) :=
        lt_trans hn_lt (lt_trans (d₂_lt_cutRule s p dp dq) hsize)
      have heq := translateFormula_neg hp_scope.isUFormula 0 0 param hp_scope hparam hp_len hn_len
      have hp' := ihp (lt_trans (d₁_lt_cutRule s p dp dq) hsize)
      have hq' := ihq (lt_trans (d₂_lt_cutRule s p dp dq) hsize)
      rw [hdp.1] at hp'
      rw [hdq.1] at hq'
      have h1 := Guarded.lift T (le_of_lt (d₁_lt_cutRule s p dp dq)) (scope hp_scope hp_len) hvalid hp'
      have h2 := Guarded.lift T (le_of_lt (d₂_lt_cutRule s p dp dq))
        (scope (IsSemiformula.neg_iff.mpr hp_scope) hn_len) hvalid hq'
      rw [heq] at h2
      exact Derivable.cut (translateFormula param p) h1 h2
    · intro s hs p hp hpU hsize
      rw [fstIdx_axm]
      exact S.theoryAxiom s p hs hp hpU hsize
  exact hcompile hbound

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

/-- A refutation in `U` yields a refutation in `T`, given the guarded rules and `∃x Dom(x)`. -/
theorem guarded_refutation {param d : V} (hparam : ParametersValid 0 0 param)
    (hbound : d < len (nth param 1)) (hd : Proof U d (^⊥ : V)) (S : GuardedRules U T param)
    (hdom : Provable T (^∃ (domainCode (^#(0 : V))))) : Provable T (^⊥ : V) := by
  have h := guarded_compile U T hparam S hd.2 hbound
  unfold Guarded at h
  rw [hd.1, translatedSequent_singleton, translate_falsum] at h
  exact discharge_guards T hdom d h

#print axioms guard_graph
#print axioms guard_shift
#print axioms free_guardBody
#print axioms guards_succ_subset
#print axioms guarded_compile
#print axioms discharge_guards
#print axioms guarded_refutation
end generic
end PA194GuardedCompiler
