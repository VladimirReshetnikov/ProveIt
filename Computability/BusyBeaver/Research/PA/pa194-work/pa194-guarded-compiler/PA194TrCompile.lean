import PA194GuardedCalculus
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The compiler for the guarded calculus

An internal derivation of a theory `U` of the arithmetic language is compiled to a guarded
derivation of the translated sequent in a theory `T` of the source language. The interface
`Interpretation U T` has no packet and no size condition: it asks for the translated axioms
and for the existential introduction at a term that is not a free variable.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (U : Theory PA194PAeq.language) [U.Δ₁] (T : Theory SourceL) [T.Δ₁]

/-- What the compiler needs from the pair of theories, stated for the translation `tr`. -/
structure Interpretation : Prop where
  /-- Every internal axiom of `U` has a guarded proof of its translation. -/
  axioms : ∀ φ : V, IsSemiformula PA194PAeq.language 0 φ → φ ∈ U.Δ₁Class →
    GDerivable T ({tr φ} : V)
  /-- Existential introduction at a term that is not a free variable. -/
  witness : ∀ p t : V, IsSemiformula PA194PAeq.language 1 p → IsTerm PA194PAeq.language t →
    (∀ j, t ≠ ^&j) →
    GDerivable T (insert (neg SourceL (tr (substs1 PA194PAeq.language t p))) ({tr (^∃ p)} : V))
  /-- The domain of the interpretation is inhabited. -/
  inhabited : Provable T (^∃ (domainCode (^#(0 : V))))

variable {U T}

theorem tr_compile {param d : V} (hid : IdentityPacket param) (I : Interpretation (V := V) U T)
    (hd : Derivation U d) (hbound : d < len (nth param 1)) :
    GDerivable T (translatedSequent param (fstIdx d)) := by
  let P : V → Prop := fun d => d < len (nth param 1) →
    ∃ n, Derivable T (guards n ∪ translatedSequent param (fstIdx d))
  have hP : 𝚺₁-Predicate P := by
    haveI : 𝚺₁-Function₂ (translatedSequent : V → V → V) := translatedSequent_defined.to_definable
    dsimp [P]
    definability
  have hparam := hid.1
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
      exact GDerivable.em hvalid (translateFormula param p)
        (translatedSequent_mem.mpr ⟨p,hp,rfl⟩) (translatedSequent_mem.mpr ⟨_,hnp,heq.symm⟩)
    · intro s hs hp hsize
      rw [fstIdx_verumIntro]
      have hlen : ∀ q ∈ s, q < len (nth param 1) := seqMembers_bounded (lt_trans (seq_lt_verumIntro s) hsize)
      exact GDerivable.verum (translatedSequent_valid hparam hs hlen)
        (translatedSequent_mem.mpr ⟨_,hp,(translate_verum param).symm⟩)
    · intro s hs p q dp dq hpq hdp hdq ihp ihq hsize
      rw [fstIdx_andIntro]
      have hpqf := IsSemiformula.and.mp (hs _ hpq)
      have hp' : GDerivable T (translatedSequent param (fstIdx dp)) :=
        ihp (lt_trans (dp_lt_andIntro s p q dp dq) hsize)
      have hq' : GDerivable T (translatedSequent param (fstIdx dq)) :=
        ihq (lt_trans (dq_lt_andIntro s p q dp dq) hsize)
      rw [hdp.1, translatedSequent_insert] at hp'
      rw [hdq.1, translatedSequent_insert] at hq'
      exact GDerivable.and_m (translatedSequent_mem.mpr
        ⟨_,hpq,(translate_and param p q hpqf.1.isUFormula hpqf.2.isUFormula).symm⟩) hp' hq'
    · intro s hs p q dp hpq hdp ih hsize
      rw [fstIdx_orIntro]
      have hpqf := IsSemiformula.or.mp (hs _ hpq)
      have hp' : GDerivable T (translatedSequent param (fstIdx dp)) :=
        ih (lt_trans (d_lt_orIntro s p q dp) hsize)
      rw [hdp.1, translatedSequent_insert, translatedSequent_insert] at hp'
      exact GDerivable.or_m (translatedSequent_mem.mpr
        ⟨_,hpq,(translate_or param p q hpqf.1.isUFormula hpqf.2.isUFormula).symm⟩) hp'
    · intro s hs p dp hp hdp ih hsize
      rw [fstIdx_allIntro]
      have hlen : ∀ q ∈ s, q < len (nth param 1) :=
        seqMembers_bounded (lt_trans (seq_lt_allIntro s p dp) hsize)
      have hdlen : dp < len (nth param 1) := lt_trans (s_lt_allIntro s p dp) hsize
      have hlen0 : ∀ q ∈ fstIdx dp, q < len (nth param 1) := fun q hq =>
        lt_trans (lt_of_lt_of_le (lt_of_mem hq) (fstIdx_le_self dp)) hdlen
      have hvalid := translatedSequent_valid hparam hs hlen
      have hall : IsSemiformula PA194PAeq.language 0 (^∀ p) := hs _ hp
      have hp1 : IsSemiformula PA194PAeq.language 1 p := by simpa using (IsSemiformula.all).mp hall
      have hplen : p < len (nth param 1) := lt_trans (lt_qqAll p) (hlen _ hp)
      have hfmem : free PA194PAeq.language p ∈ fstIdx dp := by rw [hdp.1]; simp
      have hsmem : ^∀ (shift PA194PAeq.language p) ∈ fstIdx dp := by
        rw [hdp.1, ← shift_all hp1.isUFormula]
        exact mem_bitInsert_iff.mpr (Or.inr (shift_mem_setShift hp))
      have hslen : shift PA194PAeq.language p < len (nth param 1) :=
        lt_trans (lt_qqAll _) (hlen0 _ hsmem)
      have hchild : ParametersValid 1 1 (formulaChildParameters param) := by
        simpa using formulaChildParameters_valid hparam
      have hC : IsSemiformula SourceL 1 (translateFormula (formulaChildParameters param) p) :=
        formula_scope_translate hp1.isUFormula 1 1 (formulaChildParameters param) hp1 hchild
          (by rw [hid.child_free_len]; exact hplen)
      have hfree := translateFormula_free hid hp1 hplen hslen (hlen0 _ hfmem)
      have htall : translateFormula param (^∀ p) =
          ^∀ (guardBody ^⋎ translateFormula (formulaChildParameters param) p) :=
        translate_all param p hp1.isUFormula
      have h' : GDerivable T (translatedSequent param (fstIdx dp)) := ih hdlen
      rw [hdp.1, translatedSequent_insert, hfree] at h'
      refine GDerivable.all_rel hC (by rw [← htall]; exact translatedSequent_mem.mpr ⟨_,hp,rfl⟩) ?_
      refine GDerivable.wk (IsFormulaSet.insert_iff.mpr ⟨hC.free,hvalid.setShift⟩) ?_ h'
      intro x hx
      rcases mem_bitInsert_iff.mp hx with hx | hx
      · exact mem_bitInsert_iff.mpr (Or.inl hx)
      · obtain ⟨q,hq,rfl⟩ := translatedSequent_mem.mp hx
        obtain ⟨q0,hq0,rfl⟩ := mem_setShift_iff.mp hq
        refine mem_bitInsert_iff.mpr (Or.inr (mem_setShift_iff.mpr
          ⟨translateFormula param q0,translatedSequent_mem.mpr ⟨q0,hq0,rfl⟩,?_⟩))
        exact translateFormula_shift hid (hs q0 hq0) (hlen q0 hq0)
          (hlen0 _ (by rw [hdp.1]; exact mem_bitInsert_iff.mpr (Or.inr (shift_mem_setShift hq0))))
    · intro s hs p t dp hp ht hdp ih hsize
      rw [fstIdx_exsIntro]
      have hlen : ∀ q ∈ s, q < len (nth param 1) :=
        seqMembers_bounded (lt_trans (seq_lt_exsIntro s p t dp) hsize)
      have hdlen : dp < len (nth param 1) := lt_trans (d_lt_exsIntro s p t dp) hsize
      have hlen0 : ∀ q ∈ fstIdx dp, q < len (nth param 1) := fun q hq =>
        lt_trans (lt_of_lt_of_le (lt_of_mem hq) (fstIdx_le_self dp)) hdlen
      have hvalid := translatedSequent_valid hparam hs hlen
      have hex : IsSemiformula PA194PAeq.language 0 (^∃ p) := hs _ hp
      have hp1 : IsSemiformula PA194PAeq.language 1 p := by simpa using (IsSemiformula.exs).mp hex
      have hplen : p < len (nth param 1) := lt_trans (lt_qqExs p) (hlen _ hp)
      have hsmem : substs1 PA194PAeq.language t p ∈ fstIdx dp := by rw [hdp.1]; simp
      have hslen := hlen0 _ hsmem
      have hchild : ParametersValid 1 1 (formulaChildParameters param) := by
        simpa using formulaChildParameters_valid hparam
      have hC : IsSemiformula SourceL 1 (translateFormula (formulaChildParameters param) p) :=
        formula_scope_translate hp1.isUFormula 1 1 (formulaChildParameters param) hp1 hchild
          (by rw [hid.child_free_len]; exact hplen)
      have htex : translateFormula param (^∃ p) =
          ^∃ (domainCode (^#(0 : V)) ^⋏ translateFormula (formulaChildParameters param) p) :=
        translate_exs param p hp1.isUFormula
      have h' : GDerivable T (translatedSequent param (fstIdx dp)) := ih hdlen
      rw [hdp.1, translatedSequent_insert] at h'
      by_cases hv : ∃ j, t = ^&j
      · obtain ⟨j,rfl⟩ := hv
        have hj : j < len (nth param 1) :=
          lt_trans (lt_trans (lt_qqFvar j) (t_lt_exsIntro s p (^&j) dp)) hsize
        rw [translateFormula_substs1_fvar hid hp1 hj hplen hslen] at h'
        exact GDerivable.ex_rel hC (by rw [← htex]; exact translatedSequent_mem.mpr ⟨_,hp,rfl⟩) j h'
      · have hsf : IsSemiformula PA194PAeq.language 0 (substs1 PA194PAeq.language t p) :=
          IsSemiformula.substs1 ht hp1
        have hw := I.witness p t hp1 ht (fun j hj => hv ⟨j,hj⟩)
        rw [tr_eq hid hsf hslen] at h'
        have hexmem : tr (^∃ p) ∈ translatedSequent param s :=
          translatedSequent_mem.mpr ⟨_,hp,(tr_eq hid hex (hlen _ hp)).symm⟩
        refine GDerivable.cut (tr (substs1 PA194PAeq.language t p)) h' ?_
        refine GDerivable.wk (IsFormulaSet.insert_iff.mpr
          ⟨IsSemiformula.neg_iff.mpr (tr_valid hsf),hvalid⟩) ?_ hw
        intro x hx
        rcases mem_bitInsert_iff.mp hx with hx | hx
        · exact mem_bitInsert_iff.mpr (Or.inl hx)
        · have hx' : x = tr (^∃ p) := by simpa using hx
          rw [hx']
          exact mem_bitInsert_iff.mpr (Or.inr hexmem)
    · intro s hs dp hsub hdp ih hsize
      rw [fstIdx_wkRule]
      have hlen : ∀ q ∈ s, q < len (nth param 1) := seqMembers_bounded (lt_trans (seq_lt_wkRule s dp) hsize)
      exact GDerivable.wk (translatedSequent_valid hparam hs hlen) (translatedSequent_subset hsub)
        (ih (lt_trans (d_lt_wkRule s dp) hsize))
    · intro s hs dp heq hdp ih hsize
      rw [fstIdx_shiftRule]
      have hlen : ∀ q ∈ s, q < len (nth param 1) :=
        seqMembers_bounded (lt_trans (seq_lt_shiftRule s dp) hsize)
      have hdlen : dp < len (nth param 1) := lt_trans (d_lt_shiftRule s dp) hsize
      have hlen0 : ∀ q ∈ fstIdx dp, q < len (nth param 1) := fun q hq =>
        lt_trans (lt_of_lt_of_le (lt_of_mem hq) (fstIdx_le_self dp)) hdlen
      have h' : GDerivable T (translatedSequent param (fstIdx dp)) := ih hdlen
      refine GDerivable.wk (translatedSequent_valid hparam hs hlen) ?_ h'.shift
      intro x hx
      obtain ⟨y,hy,rfl⟩ := mem_setShift_iff.mp hx
      obtain ⟨p,hp,rfl⟩ := translatedSequent_mem.mp hy
      have hmem : shift PA194PAeq.language p ∈ s := by
        rw [heq]
        exact shift_mem_setShift hp
      exact translatedSequent_mem.mpr ⟨shift PA194PAeq.language p,hmem,
        (translateFormula_shift hid (hdp.isFormulaSet p hp) (hlen0 p hp) (hlen _ hmem)).symm⟩
    · intro s hs p dp dq hdp hdq ihp ihq hsize
      rw [fstIdx_cutRule]
      have hn_mem : neg PA194PAeq.language p ∈ fstIdx dq := by rw [hdq.1]; simp
      have hp_scope : IsSemiformula PA194PAeq.language 0 p := hdp.isFormulaSet p (by simp)
      have hp_len : p < len (nth param 1) := lt_trans (p_lt_cutRule s p dp dq) hsize
      have hn_lt : neg PA194PAeq.language p < dq := lt_of_lt_of_le (lt_of_mem hn_mem) (fstIdx_le_self dq)
      have hn_len : neg PA194PAeq.language p < len (nth param 1) :=
        lt_trans hn_lt (lt_trans (d₂_lt_cutRule s p dp dq) hsize)
      have heq := translateFormula_neg hp_scope.isUFormula 0 0 param hp_scope hparam hp_len hn_len
      have hp' : GDerivable T (translatedSequent param (fstIdx dp)) :=
        ihp (lt_trans (d₁_lt_cutRule s p dp dq) hsize)
      have hq' : GDerivable T (translatedSequent param (fstIdx dq)) :=
        ihq (lt_trans (d₂_lt_cutRule s p dp dq) hsize)
      rw [hdp.1, translatedSequent_insert] at hp'
      rw [hdq.1, translatedSequent_insert, heq] at hq'
      exact GDerivable.cut (translateFormula param p) hp' hq'
    · intro s hs p hp hpU hsize
      rw [fstIdx_axm]
      have hlen : ∀ q ∈ s, q < len (nth param 1) := seqMembers_bounded (lt_trans (seq_lt_axm s p) hsize)
      refine GDerivable.wk (translatedSequent_valid hparam hs hlen) ?_ (I.axioms p (hs p hp) hpU)
      intro x hx
      have hx' : x = tr p := by simpa using hx
      rw [hx']
      exact translatedSequent_mem.mpr ⟨p,hp,(tr_eq hid (hs p hp) (hlen p hp)).symm⟩
  exact hcompile hbound

/-- A refutation in `U` yields a refutation in `T` when `T` interprets `U`. -/
theorem refutation_of_interpretation (I : Interpretation (V := V) U T) {d : V}
    (hd : Proof U d (^⊥ : V)) : Provable T (^⊥ : V) := by
  have hid := idParam_identity (d + 1 : V)
  have h := tr_compile hid I hd.2 (by simp)
  rw [hd.1, translatedSequent_singleton, translate_falsum] at h
  exact GDerivable.root I.inhabited h

#print axioms tr_compile
#print axioms refutation_of_interpretation
end generic
end PA194GuardedCompiler
