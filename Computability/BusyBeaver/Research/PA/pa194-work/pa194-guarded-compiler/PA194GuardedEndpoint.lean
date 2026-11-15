import PA194TranslateSubst
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The guarded compiler with the syntactic rules discharged

For an identity packet the shift rule, the universal rule and the existential rule with a free
variable as witness are theorems. What remains is the existential rule for a witness that is a
function term, the translated theory axioms, and the inhabitation of the domain.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (U : Theory PA194PAeq.language) [U.Δ₁] (T : Theory SourceL) [T.Δ₁]

/-- The existential rule of the guarded compiler when the witness is a free variable. -/
theorem exsRule_guarded_fvar {param : V} (hid : IdentityPacket param) (s p j d : V)
    (hs : IsFormulaSet PA194PAeq.language s) (hmem : ^∃ p ∈ s)
    (hd : DerivationOf U d (insert (substs1 PA194PAeq.language (^&j) p) s))
    (hsize : exsIntro s p (^&j) d < len (nth param 1))
    (h : Guarded T param d (fstIdx d)) : Guarded T param (exsIntro s p (^&j) d) s := by
  have hlen : ∀ q ∈ s, q < len (nth param 1) :=
    seqMembers_bounded (lt_trans (seq_lt_exsIntro s p (^&j) d) hsize)
  have hdlen : d < len (nth param 1) := lt_trans (d_lt_exsIntro s p (^&j) d) hsize
  have hlen0 : ∀ q ∈ fstIdx d, q < len (nth param 1) := fun q hq =>
    lt_trans (lt_of_lt_of_le (lt_of_mem hq) (fstIdx_le_self d)) hdlen
  have hvalid := translatedSequent_valid hid.1 hs hlen
  have hex : IsSemiformula PA194PAeq.language 0 (^∃ p) := hs _ hmem
  have hp : IsSemiformula PA194PAeq.language 1 p := by simpa using (IsSemiformula.exs).mp hex
  have hplen : p < len (nth param 1) := lt_trans (lt_qqExs p) (hlen _ hmem)
  have hjt : j < exsIntro s p (^&j) d := lt_trans (lt_qqFvar j) (t_lt_exsIntro s p (^&j) d)
  have hj : j < len (nth param 1) := lt_trans hjt hsize
  have hsmem : substs1 PA194PAeq.language (^&j) p ∈ fstIdx d := by rw [hd.1]; simp
  have hslen := hlen0 _ hsmem
  have hchild : ParametersValid 1 1 (formulaChildParameters param) := by
    simpa using formulaChildParameters_valid hid.1
  have hC : IsSemiformula SourceL 1 (translateFormula (formulaChildParameters param) p) :=
    formula_scope_translate hp.isUFormula 1 1 (formulaChildParameters param) hp hchild
      (by rw [hid.child_free_len]; exact hplen)
  have hsub := translateFormula_substs1_fvar hid hp hj hplen hslen
  have htex : translateFormula param (^∃ p) =
      ^∃ (domainCode (^#(0 : V)) ^⋏ translateFormula (formulaChildParameters param) p) :=
    translate_exs param p hp.isUFormula
  have hd0 : IsSemiformula SourceL 1 (domainCode (^#(0 : V))) := domainBody_valid
  have hjterm : IsTerm SourceL (^&j : V) := by simp
  have hw : IsSemitermVec SourceL 1 0 (?[^&j] : V) := by simp
  have hinst : substs1 SourceL (^&j)
        (domainCode (^#(0 : V)) ^⋏ translateFormula (formulaChildParameters param) p) =
      domainCode (^&j) ^⋏
        substs1 SourceL (^&j) (translateFormula (formulaChildParameters param) p) := by
    show subst SourceL (?[^&j] : V)
        (domainCode (^#(0 : V)) ^⋏ translateFormula (formulaChildParameters param) p) =
      domainCode (^&j) ^⋏
        subst SourceL (?[^&j] : V) (translateFormula (formulaChildParameters param) p)
    rw [substs_and hd0.isUFormula hC.isUFormula,
      domainCode_subst (show IsSemiterm SourceL 1 (^#(0 : V)) by simp) hw, termSubst_bvar]
    simp
  have h0 : Derivable T (guards d ∪ translatedSequent param (fstIdx d)) := h
  show Derivable T (guards (exsIntro s p (^&j) d) ∪ translatedSequent param s)
  have hΓ : IsFormulaSet SourceL (guards (exsIntro s p (^&j) d) ∪ translatedSequent param s) :=
    IsFormulaSet.union.mpr ⟨guards_valid _,hvalid⟩
  refine Derivable.ex_m
    (p := domainCode (^#(0 : V)) ^⋏ translateFormula (formulaChildParameters param) p)
    (t := ^&j) ?_ hjterm ?_
  · rw [← htex]
    exact mem_cup_iff.mpr (Or.inr (translatedSequent_mem.mpr ⟨_,hmem,rfl⟩))
  · rw [hinst]
    have hCj : IsFormula SourceL
        (substs1 SourceL (^&j) (translateFormula (formulaChildParameters param) p)) :=
      IsSemiformula.substs1 hjterm hC
    have hDj : IsFormula SourceL (domainCode (^&j : V)) := domainCode_valid hjterm
    have hand : IsFormula SourceL (domainCode (^&j : V) ^⋏
        substs1 SourceL (^&j) (translateFormula (formulaChildParameters param) p)) :=
      IsSemiformula.and.mpr ⟨hDj,hCj⟩
    refine Derivable.and_m (p := domainCode (^&j : V))
      (q := substs1 SourceL (^&j) (translateFormula (formulaChildParameters param) p))
      (mem_bitInsert_iff.mpr (Or.inl rfl)) ?_ ?_
    · refine Derivable.em (IsFormulaSet.insert_iff.mpr ⟨hDj,IsFormulaSet.insert_iff.mpr ⟨hand,hΓ⟩⟩)
        (domainCode (^&j)) (mem_bitInsert_iff.mpr (Or.inl rfl)) ?_
      exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr
        (mem_cup_iff.mpr (Or.inl (mem_guards.mpr ⟨j,hjt,rfl⟩))))))
    · refine Derivable.wk (IsFormulaSet.insert_iff.mpr ⟨hCj,IsFormulaSet.insert_iff.mpr ⟨hand,hΓ⟩⟩)
        ?_ h0
      intro x hx
      rw [hd.1, translatedSequent_insert, hsub] at hx
      rcases mem_cup_iff.mp hx with hx | hx
      · exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr
          (Or.inl (guards_mono (le_of_lt (d_lt_exsIntro s p (^&j) d)) hx))))))
      · rcases mem_bitInsert_iff.mp hx with hx | hx
        · exact mem_bitInsert_iff.mpr (Or.inl hx)
        · exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr
            (mem_cup_iff.mpr (Or.inr hx)))))

/-- The rules that are still hypotheses: the existential rule for a witness that is not a free
variable, and the theory axioms. -/
structure OpenGuardedRules (param : V) : Prop where
  exsRule : ∀ s p t d, IsFormulaSet PA194PAeq.language s → ^∃ p ∈ s → IsTerm PA194PAeq.language t →
    (∀ j, t ≠ ^&j) →
    DerivationOf U d (insert (substs1 PA194PAeq.language t p) s) →
    exsIntro s p t d < len (nth param 1) →
    Guarded T param d (fstIdx d) → Guarded T param (exsIntro s p t d) s
  theoryAxiom : ∀ s p, IsFormulaSet PA194PAeq.language s → p ∈ s → p ∈ U.Δ₁Class →
    axm s p < len (nth param 1) → Guarded T param (axm s p) s

theorem guardedRules_of_open {param : V} (hid : IdentityPacket param)
    (R : OpenGuardedRules U T param) : GuardedRules U T param where
  allRule := fun s p d hs hp hd hsize h => allRule_guarded U T hid s p d hs hp hd hsize h
  exsRule := by
    intro s p t d hs hp ht hd hsize h
    by_cases hv : ∃ j, t = ^&j
    · obtain ⟨j,rfl⟩ := hv
      exact exsRule_guarded_fvar U T hid s p j d hs hp hd hsize h
    · exact R.exsRule s p t d hs hp ht (fun j hj => hv ⟨j,hj⟩) hd hsize h
  shiftRule := fun s d hs heq hd hsize h => shiftRule_guarded U T hid s d hs heq hd hsize h
  theoryAxiom := R.theoryAxiom

/-- A translated axiom with a proof of its own gives the guarded axiom leaf. -/
theorem theoryAxiom_guarded {param : V} (hparam : ParametersValid 0 0 param)
    (hsupply : ∀ p : V, IsSemiformula PA194PAeq.language 0 p → p ∈ U.Δ₁Class →
      p < len (nth param 1) → Provable T (translateFormula param p)) :
    ∀ s p, IsFormulaSet PA194PAeq.language s → p ∈ s → p ∈ U.Δ₁Class →
      axm s p < len (nth param 1) → Guarded T param (axm s p) s := by
  intro s p hs hp hu hsize
  have hlen : ∀ q ∈ s, q < len (nth param 1) := seqMembers_bounded (lt_trans (seq_lt_axm s p) hsize)
  have hvalid := translatedSequent_valid hparam hs hlen
  have hd := (hsupply p (hs p hp) hu (hlen p hp)).toDerivable
  show Derivable T (guards (axm s p) ∪ translatedSequent param s)
  refine Derivable.wk (IsFormulaSet.union.mpr ⟨guards_valid _,hvalid⟩) ?_ hd
  intro x hx
  have hx' : x = translateFormula param p := by simpa using hx
  subst hx'
  exact mem_cup_iff.mpr (Or.inr (translatedSequent_mem.mpr ⟨p,hp,rfl⟩))

/-- A refutation in `U` yields a refutation in `T` when, for every identity packet, the open
rules are supplied, and `T` proves `∃x Dom(x)`. -/
theorem refutation_of_open_rules
    (hdom : Provable T (^∃ (domainCode (^#(0 : V)))))
    (hrules : ∀ param : V, IdentityPacket param → OpenGuardedRules U T param)
    {d : V} (hd : Proof U d (^⊥ : V)) : Provable T (^⊥ : V) := by
  obtain ⟨param,hid,hlen⟩ := identityPacket_exists (d+1)
  exact guarded_refutation U T hid.1 (by rw [hlen]; exact lt_add_one d) hd
    (guardedRules_of_open U T hid (hrules param hid)) hdom

#print axioms exsRule_guarded_fvar
#print axioms guardedRules_of_open
#print axioms theoryAxiom_guarded
#print axioms refutation_of_open_rules
end generic
end PA194GuardedCompiler
