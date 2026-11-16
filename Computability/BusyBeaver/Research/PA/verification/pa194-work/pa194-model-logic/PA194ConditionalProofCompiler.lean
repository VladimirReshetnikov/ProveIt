import PA194TranslatedStructuralRules
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194FormulaDispatcher
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (U : Theory PA194PAeq.language) [U.Δ₁] (T : Theory SourceL) [T.Δ₁]

/-- The remaining quantified, shift, and source-theory-axiom rule suppliers.
Each consumes the already compiled premise when a rule has one. -/
structure RemainingRules (param : V) : Prop where
  allRule : ∀ s p d, IsFormulaSet PA194PAeq.language s → ^∀ p ∈ s →
    DerivationOf U d (insert (free PA194PAeq.language p) (setShift PA194PAeq.language s)) →
    allIntro s p d < len (nth param 1) →
    (∃ e, DerivationOf T e (translatedSequent param (fstIdx d))) →
    ∃ e, DerivationOf T e (translatedSequent param s)
  exsRule : ∀ s p t d, IsFormulaSet PA194PAeq.language s → ^∃ p ∈ s → IsTerm PA194PAeq.language t →
    DerivationOf U d (insert (substs1 PA194PAeq.language t p) s) →
    exsIntro s p t d < len (nth param 1) →
    (∃ e, DerivationOf T e (translatedSequent param (fstIdx d))) →
    ∃ e, DerivationOf T e (translatedSequent param s)
  shiftRule : ∀ s d, IsFormulaSet PA194PAeq.language s → s = setShift PA194PAeq.language (fstIdx d) →
    Derivation U d → shiftRule s d < len (nth param 1) →
    (∃ e, DerivationOf T e (translatedSequent param (fstIdx d))) →
    ∃ e, DerivationOf T e (translatedSequent param s)
  theoryAxiom : ∀ s p, IsFormulaSet PA194PAeq.language s → p ∈ s → p ∈ U.Δ₁Class →
    axm s p < len (nth param 1) → ∃ e, DerivationOf T e (translatedSequent param s)

theorem seqMembers_bounded {s bound : V} (hs : s < bound) :
    ∀ q ∈ s, q < bound := by
  intro q hq
  exact lt_trans (lt_of_mem hq) hs

theorem conditional_compile {param d : V} (hparam : ParametersValid 0 0 param)
    (S : RemainingRules U T param) (hd : Derivation U d)
    (hbound : d < len (nth param 1)) :
    ∃ e, DerivationOf T e (translatedSequent param (fstIdx d)) := by
  let P : V → Prop := fun d => d < len (nth param 1) →
    ∃ e, DerivationOf T e (translatedSequent param (fstIdx d))
  have hP : 𝚺₁-Predicate P := by
    haveI : 𝚺₁-Function₂ (translatedSequent : V → V → V) := translatedSequent_defined.to_definable
    dsimp [P]
    definability
  have hcompile : P d := by
    apply Derivation.induction1 𝚺 hP hd
    · intro s hs p hp hnp hsize
      have hlen : ∀ q ∈ s, q < len (nth param 1) := seqMembers_bounded (lt_trans (seq_lt_axL s p) hsize)
      refine ⟨compileAxiom param s p,?_,compileAxiom_valid T hparam hs hlen hp hnp⟩
      simp [compileAxiom_sequent]
    · intro s hs hp hsize
      have hlen : ∀ q ∈ s, q < len (nth param 1) := seqMembers_bounded (lt_trans (seq_lt_verumIntro s) hsize)
      refine ⟨compileVerum param s,?_,compileVerum_valid T hparam hs hlen hp⟩
      simp [compileVerum_sequent]
    · intro s hs p q dp dq hpq hdp hdq ihp ihq hsize
      obtain ⟨ep,hep⟩ := ihp (lt_trans (dp_lt_andIntro s p q dp dq) hsize)
      obtain ⟨eq,heq⟩ := ihq (lt_trans (dq_lt_andIntro s p q dp dq) hsize)
      have hep' : DerivationOf T ep (translatedSequent param (insert p s)) := by simpa [hdp.1] using hep
      have heq' : DerivationOf T eq (translatedSequent param (insert q s)) := by simpa [hdq.1] using heq
      refine ⟨compileAnd param s p q ep eq,?_,compileAnd_valid T hpq hs hep' heq'⟩
      simp [compileAnd_sequent]
    · intro s hs p q dp hpq hdp ih hsize
      obtain ⟨ep,hep⟩ := ih (lt_trans (d_lt_orIntro s p q dp) hsize)
      have hep' : DerivationOf T ep (translatedSequent param (insert p (insert q s))) := by simpa [hdp.1] using hep
      refine ⟨compileOr param s p q ep,?_,compileOr_valid T hpq hs hep'⟩
      simp [compileOr_sequent]
    · intro s hs p dp hp hdp ih hsize
      have hchild := ih (lt_trans (s_lt_allIntro s p dp) hsize)
      simpa using S.allRule s p dp hs hp hdp hsize hchild
    · intro s hs p t dp hp ht hdp ih hsize
      have hchild := ih (lt_trans (d_lt_exsIntro s p t dp) hsize)
      simpa using S.exsRule s p t dp hs hp ht hdp hsize hchild
    · intro s hs dp hsub hdp ih hsize
      have hlen : ∀ q ∈ s, q < len (nth param 1) := seqMembers_bounded (lt_trans (seq_lt_wkRule s dp) hsize)
      obtain ⟨ep,hep⟩ := ih (lt_trans (d_lt_wkRule s dp) hsize)
      refine ⟨compileWeak param s ep,?_,compileWeak_valid T hparam hs hlen hsub hep⟩
      simp [compileWeak_sequent]
    · intro s hs dp heq hdp ih hsize
      have hchild := ih (lt_trans (d_lt_shiftRule s dp) hsize)
      simpa using S.shiftRule s dp hs heq hdp hsize hchild
    · intro s hs p dp dq hdp hdq ihp ihq hsize
      have hn_mem : neg PA194PAeq.language p ∈ fstIdx dq := by rw [hdq.1]; simp
      have hp_scope : IsSemiformula PA194PAeq.language 0 p := hdp.isFormulaSet p (by simp)
      have hp_len : p < len (nth param 1) := lt_trans (p_lt_cutRule s p dp dq) hsize
      have hn_lt : neg PA194PAeq.language p < dq := lt_of_lt_of_le (lt_of_mem hn_mem) (fstIdx_le_self dq)
      have hn_len : neg PA194PAeq.language p < len (nth param 1) := lt_trans hn_lt (lt_trans (d₂_lt_cutRule s p dp dq) hsize)
      obtain ⟨ep,hep⟩ := ihp (lt_trans (d₁_lt_cutRule s p dp dq) hsize)
      obtain ⟨eq,heq⟩ := ihq (lt_trans (d₂_lt_cutRule s p dp dq) hsize)
      have hep' : DerivationOf T ep (translatedSequent param (insert p s)) := by simpa [hdp.1] using hep
      have heq' : DerivationOf T eq (translatedSequent param (insert (neg PA194PAeq.language p) s)) := by simpa [hdq.1] using heq
      refine ⟨compileCut param s p ep eq,?_,compileCut_valid T hp_scope hparam hp_len hn_len hep' heq'⟩
      simp [compileCut_sequent]
    · intro s hs p hp hpU hsize
      simpa using S.theoryAxiom s p hs hp hpU hsize
  exact hcompile hbound
#print axioms conditional_compile
end generic
end PA194FormulaDispatcher
