import PA194ValueBody
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The translated name formulas as explicit source codes

`tr (nameAll s s')`, `tr (uniq s)` and `tr (exName s)` are written out for terms `s`, `s'` of
arity zero. The only parts that depend on the terms are their value formulas `valBody s` at a
bound variable; everything else is a fixed arrangement of the domain, equality and
order-isomorphism formulas. These are identities between codes.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Terms without bound variables -/

/-- A term of arity zero is not changed by the shift of bound variables. -/
theorem termBShift_closed :
    ∀ s : V, IsSemiterm PA194PAeq.language 0 s → termBShift PA194PAeq.language s = s := by
  refine term_induction (P := fun s : V => termBShift PA194PAeq.language s = s)
    (by definability) ?_ ?_ ?_ ?_ ?_
  · intro i
    simp
  · unfold zeroT
    rw [termBShift_func (by simp) (by simp)]
    simp
  · intro s hs ih
    unfold succT
    rw [termBShift_func (by simp) (by simp [hs.isUTerm]), termBShiftVec_cons₁ hs.isUTerm, ih]
  · intro s s' hs hs' ih ih'
    unfold addT
    rw [termBShift_func (by simp) (by simp [hs.isUTerm,hs'.isUTerm]),
      termBShiftVec_cons₂ hs.isUTerm hs'.isUTerm, ih, ih']
  · intro s s' hs hs' ih ih'
    unfold mulT
    rw [termBShift_func (by simp) (by simp [hs.isUTerm,hs'.isUTerm]),
      termBShiftVec_cons₂ hs.isUTerm hs'.isUTerm, ih, ih']

/-! ### Packets under formula binders -/

theorem FreeId.formulaChild {k n P : V} (hP : ParametersValid k n P) (h : FreeId P) :
    FreeId (formulaChildParameters P) := by
  have h1 := h.step (r := termBShift SourceL (nth P 2)) hP
  intro i hi
  have e : nth (formulaChildParameters P) 1 = shiftTerms (nth P 1) := by
    simp [formulaChildParameters]
  rw [e] at hi ⊢
  simpa using h1 i (by simpa using hi)
theorem formulaChild_free_len {k n P : V} (hP : ParametersValid k n P) :
    len (nth (formulaChildParameters P) 1) = len (nth P 1) := by
  simp [formulaChildParameters, shiftTerms_length hP.2.1]

/-- The source formula `∃v∃w (a ∧ b ∧ orderIso(v, w))`; `a` and `b` are written under the two
binders, `v` being the outer one. -/
noncomputable def eqForm (a b : V) : V :=
  ^∃ (^∃ (a ^⋏ (b ^⋏ orderIsoCode (^#(1 : V)) (^#(0 : V)))))

theorem tf_peq (P a b : V) (ha : IsUTerm PA194PAeq.language a) (hb : IsUTerm PA194PAeq.language b) :
    translateFormula P (peq a b) =
      eqForm (translate (binaryParameters P 1) a) (translate (binaryParameters P 0) b) := by
  have hv : IsUTermVec PA194PAeq.language 2 (?[a,b] : V) := by simp [ha,hb]
  have h := translate_rel P (2 : V) 0 (?[a,b] : V) isRel_eq hv
  have hn0 : nth (?[a,b] : V) 0 = a := by simp
  have hn1 : nth (?[a,b] : V) 1 = b := by simp
  rw [hn0, hn1] at h
  unfold atomicEquality at h
  unfold peq eqForm
  exact h
theorem tf_neg_peq (P a b : V) (ha : IsUTerm PA194PAeq.language a)
    (hb : IsUTerm PA194PAeq.language b) :
    translateFormula P (neg PA194PAeq.language (peq a b)) =
      neg SourceL (translateFormula P (peq a b)) := by
  have hv : IsUTermVec PA194PAeq.language 2 (?[a,b] : V) := by simp [ha,hb]
  have h := translate_nrel P (2 : V) 0 (?[a,b] : V) isRel_eq hv
  have h' := translate_rel P (2 : V) 0 (?[a,b] : V) isRel_eq hv
  unfold peq
  rw [neg_rel isRel_eq hv, h, h']

/-- The value of a term of arity zero under a binary packet. -/
theorem tl_term {k n P s j : V} (hP : ParametersValid k n P) (hfree : FreeId P) (hj : j < 2)
    (hs : IsSemiterm PA194PAeq.language 0 s) (hlen : s < len (nth P 1)) :
    translate (binaryParameters P j) s = substs1 SourceL (^#j) (valBody s) := by
  have h := translate_lift (binaryParameters_valid hP hj) (hfree.binary j hP) hs
    (by rw [binary_free_len j hP]; exact hlen)
  have hr : nth (binaryParameters P j) 2 = ^#j := by simp [binaryParameters]
  rw [hr] at h
  exact h
/-- The value of a bound variable under a binary packet. -/
theorem tl_bvar (P i j : V) :
    translate (binaryParameters P j) (^#i) =
      variableValue (^#j) (nth (shiftTerms (shiftTerms (nth P 0))) i) := by
  rw [translate_bound]
  simp [binaryParameters]

theorem shiftTerms_one (a : V) (ha : IsUTerm SourceL a) :
    shiftTerms (?[a] : V) = ?[termBShift SourceL a] := by
  unfold shiftTerms
  have hl : len (?[a] : V) = 1 := by simp
  rw [hl, termBShiftVec_cons₁ ha]
theorem shiftTerms_two (a b : V) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b) :
    shiftTerms (?[a,b] : V) = ?[termBShift SourceL a, termBShift SourceL b] := by
  unfold shiftTerms
  have hl : len (?[a,b] : V) = 2 := by simp [one_add_one_eq_two]
  rw [hl, termBShiftVec_cons₂ ha hb]
theorem shiftTerms_nil : shiftTerms (0 : V) = 0 := by
  unfold shiftTerms
  simp

theorem bound_one (L : V) :
    nth (formulaChildParameters (idParam L)) 0 = (?[^#(0 : V)] : V) := by
  simp [formulaChildParameters, idParam, shiftTerms_nil]
theorem bound_two (L : V) :
    nth (formulaChildParameters (formulaChildParameters (idParam L))) 0 =
      (?[^#(0 : V), ^#(1 : V)] : V) := by
  have h1 := bound_one L
  have e : nth (formulaChildParameters (formulaChildParameters (idParam L))) 0 =
      (^#(0 : V)) ∷ shiftTerms (nth (formulaChildParameters (idParam L)) 0) := by
    simp [formulaChildParameters]
  rw [e, h1, shiftTerms_one _ (by simp)]
  simp
theorem ss_one : shiftTerms (shiftTerms (?[^#(0 : V)] : V)) = (?[^#(2 : V)] : V) := by
  rw [shiftTerms_one _ (by simp), shiftTerms_one _ (by simp)]
  simp [one_add_one_eq_two]
theorem ss_two :
    shiftTerms (shiftTerms (?[^#(0 : V), ^#(1 : V)] : V)) = (?[^#(2 : V), ^#(3 : V)] : V) := by
  rw [shiftTerms_two _ _ (by simp) (by simp), shiftTerms_two _ _ (by simp) (by simp)]
  simp [one_add_one_eq_two, two_add_one_eq_three]

theorem valid_one (L : V) : ParametersValid 1 1 (formulaChildParameters (idParam L)) := by
  simpa using formulaChildParameters_valid (idParam_identity L).1
theorem valid_two (L : V) :
    ParametersValid 2 2 (formulaChildParameters (formulaChildParameters (idParam L))) := by
  simpa [one_add_one_eq_two] using formulaChildParameters_valid (valid_one L)
theorem freeId_one (L : V) : FreeId (formulaChildParameters (idParam L)) :=
  (idParam_freeId L).formulaChild (idParam_identity L).1
theorem freeId_two (L : V) : FreeId (formulaChildParameters (formulaChildParameters (idParam L))) :=
  (freeId_one L).formulaChild (valid_one L)
theorem len_one (L : V) : len (nth (formulaChildParameters (idParam L)) 1) = L := by
  rw [formulaChild_free_len (idParam_identity L).1]
  simp
theorem len_two (L : V) :
    len (nth (formulaChildParameters (formulaChildParameters (idParam L))) 1) = L := by
  rw [formulaChild_free_len (valid_one L), len_one]

/-! ### Atoms under one and two binders -/

/-- `x = s` under the binder of `x`. -/
theorem atom_one {s L : V} (hs : IsSemiterm PA194PAeq.language 0 s) (hL : s < L) :
    translateFormula (formulaChildParameters (idParam L)) (peq (^#(0 : V)) s) =
      eqForm (variableValue (^#(1 : V)) (^#(2 : V))) (substs1 SourceL (^#(0 : V)) (valBody s)) := by
  rw [tf_peq _ _ _ (by simp) hs.isUTerm, tl_bvar, bound_one, ss_one,
    tl_term (valid_one L) (freeId_one L) (by simp) hs (by rw [len_one]; exact hL)]
  simp
/-- `x = s` under the binders of `x` and `y`, `y` being the inner one. -/
theorem atom_two_outer {s L : V} (hs : IsSemiterm PA194PAeq.language 0 s) (hL : s < L) :
    translateFormula (formulaChildParameters (formulaChildParameters (idParam L)))
        (peq (^#(1 : V)) s) =
      eqForm (variableValue (^#(1 : V)) (^#(3 : V))) (substs1 SourceL (^#(0 : V)) (valBody s)) := by
  rw [tf_peq _ _ _ (by simp) hs.isUTerm, tl_bvar, bound_two, ss_two,
    tl_term (valid_two L) (freeId_two L) (by simp) hs (by rw [len_two]; exact hL)]
  simp
/-- `y = s` under the binders of `x` and `y`. -/
theorem atom_two_inner {s L : V} (hs : IsSemiterm PA194PAeq.language 0 s) (hL : s < L) :
    translateFormula (formulaChildParameters (formulaChildParameters (idParam L)))
        (peq (^#(0 : V)) s) =
      eqForm (variableValue (^#(1 : V)) (^#(2 : V))) (substs1 SourceL (^#(0 : V)) (valBody s)) := by
  rw [tf_peq _ _ _ (by simp) hs.isUTerm, tl_bvar, bound_two, ss_two,
    tl_term (valid_two L) (freeId_two L) (by simp) hs (by rw [len_two]; exact hL)]
  simp
/-- `x = y` under the binders of `x` and `y`. -/
theorem atom_two_vars (L : V) :
    translateFormula (formulaChildParameters (formulaChildParameters (idParam L)))
        (peq (^#(1 : V)) (^#(0 : V))) =
      eqForm (variableValue (^#(1 : V)) (^#(3 : V))) (variableValue (^#(0 : V)) (^#(2 : V))) := by
  rw [tf_peq _ _ _ (by simp) (by simp), tl_bvar, tl_bvar, bound_two, ss_two]
  simp

theorem lt_peq_right (a b : V) : b < peq a b := by
  unfold peq
  simpa using (nth_lt_qqRel_of_lt (k := (2 : V)) (r := (0 : V)) (v := (?[a,b] : V))
    (i := (1 : V)) (by simp))
theorem lt_npeq_right (a b : V) (ha : IsUTerm PA194PAeq.language a)
    (hb : IsUTerm PA194PAeq.language b) : b < neg PA194PAeq.language (peq a b) := by
  have hv : IsUTermVec PA194PAeq.language 2 (?[a,b] : V) := by simp [ha,hb]
  unfold peq
  rw [neg_rel isRel_eq hv]
  simpa using (nth_lt_qqNRel_of_lt (k := (2 : V)) (r := (0 : V)) (v := (?[a,b] : V))
    (i := (1 : V)) (by simp))

/-! ### The three formulas -/

/-- The translation of "every name of `s` is a name of `s'`". -/
theorem tr_nameAll {s s' : V} (hs : IsSemiterm PA194PAeq.language 0 s)
    (hs' : IsSemiterm PA194PAeq.language 0 s') :
    tr (nameAll s s') = ^∀ (guardBody ^⋎
      (neg SourceL (eqForm (variableValue (^#(1 : V)) (^#(2 : V)))
          (substs1 SourceL (^#(0 : V)) (valBody s))) ^⋎
        eqForm (variableValue (^#(1 : V)) (^#(2 : V)))
          (substs1 SourceL (^#(0 : V)) (valBody s')))) := by
  have h0 : IsSemiterm PA194PAeq.language 1 (^#(0 : V)) := by simp
  have hs1 : IsSemiterm PA194PAeq.language 1 s := by
    simpa [termBShift_closed s hs] using bShift_valid hs
  have hs1' : IsSemiterm PA194PAeq.language 1 s' := by
    simpa [termBShift_closed s' hs'] using bShift_valid hs'
  have ha : IsSemiformula PA194PAeq.language 1 (neg PA194PAeq.language (peq (^#(0 : V)) s)) :=
    IsSemiformula.neg_iff.mpr (peq_valid h0 hs1)
  have hb : IsSemiformula PA194PAeq.language 1 (peq (^#(0 : V)) s') := peq_valid h0 hs1'
  have hp : IsSemiformula PA194PAeq.language 1
      (neg PA194PAeq.language (peq (^#(0 : V)) s) ^⋎ peq (^#(0 : V)) s') :=
    IsSemiformula.or.mpr ⟨ha,hb⟩
  have l1 : s < (neg PA194PAeq.language (peq (^#(0 : V)) s) ^⋎ peq (^#(0 : V)) s') + 1 :=
    lt_trans (lt_trans (lt_npeq_right _ _ (by simp) hs.isUTerm) (lt_qqOr_left _ _)) (lt_add_one _)
  have l2 : s' < (neg PA194PAeq.language (peq (^#(0 : V)) s) ^⋎ peq (^#(0 : V)) s') + 1 :=
    lt_trans (lt_trans (lt_peq_right _ _) (lt_qqOr_right _ _)) (lt_add_one _)
  unfold nameAll
  rw [termBShift_closed s hs, termBShift_closed s' hs', tr_all hp]
  unfold trBody
  rw [translate_or _ _ _ ha.isUFormula hb.isUFormula, tf_neg_peq _ _ _ (by simp) hs.isUTerm,
    atom_one hs l1, atom_one hs' l2]

/-- The translation of "`s` has a name". -/
theorem tr_exName {s : V} (hs : IsSemiterm PA194PAeq.language 0 s) :
    tr (exName s) = ^∃ (domainCode (^#(0 : V)) ^⋏
      eqForm (variableValue (^#(1 : V)) (^#(2 : V))) (substs1 SourceL (^#(0 : V)) (valBody s))) := by
  have h0 : IsSemiterm PA194PAeq.language 1 (^#(0 : V)) := by simp
  have hs1 : IsSemiterm PA194PAeq.language 1 s := by
    simpa [termBShift_closed s hs] using bShift_valid hs
  have hp : IsSemiformula PA194PAeq.language 1 (peq (^#(0 : V)) s) := peq_valid h0 hs1
  have l1 : s < peq (^#(0 : V)) s + 1 := lt_trans (lt_peq_right _ _) (lt_add_one _)
  unfold exName
  rw [termBShift_closed s hs, tr_exs hp]
  unfold trBody
  rw [atom_one hs l1]

/-- The translation of "any two names of `s` are equal". -/
theorem tr_uniq {s : V} (hs : IsSemiterm PA194PAeq.language 0 s) :
    tr (uniq s) = ^∀ (guardBody ^⋎ ^∀ (guardBody ^⋎
      (neg SourceL (eqForm (variableValue (^#(1 : V)) (^#(3 : V)))
          (substs1 SourceL (^#(0 : V)) (valBody s))) ^⋎
        (neg SourceL (eqForm (variableValue (^#(1 : V)) (^#(2 : V)))
            (substs1 SourceL (^#(0 : V)) (valBody s))) ^⋎
          eqForm (variableValue (^#(1 : V)) (^#(3 : V)))
            (variableValue (^#(0 : V)) (^#(2 : V))))))) := by
  have h1 : IsSemiterm PA194PAeq.language 2 (^#(1 : V)) := by simp
  have h0 : IsSemiterm PA194PAeq.language 2 (^#(0 : V)) := by simp
  have hs2 : IsSemiterm PA194PAeq.language 2 s := by
    have h := IsSemiterm.termBShift (bShift_valid hs)
    rw [termBShift_closed s hs, termBShift_closed s hs] at h
    simpa [one_add_one_eq_two] using h
  have ha : IsSemiformula PA194PAeq.language 2 (neg PA194PAeq.language (peq (^#(1 : V)) s)) :=
    IsSemiformula.neg_iff.mpr (peq_valid h1 hs2)
  have hb : IsSemiformula PA194PAeq.language 2 (neg PA194PAeq.language (peq (^#(0 : V)) s)) :=
    IsSemiformula.neg_iff.mpr (peq_valid h0 hs2)
  have hc : IsSemiformula PA194PAeq.language 2 (peq (^#(1 : V)) (^#(0 : V))) := peq_valid h1 h0
  have hbc : IsSemiformula PA194PAeq.language 2
      (neg PA194PAeq.language (peq (^#(0 : V)) s) ^⋎ peq (^#(1 : V)) (^#(0 : V))) :=
    IsSemiformula.or.mpr ⟨hb,hc⟩
  have hq : IsSemiformula PA194PAeq.language 2
      (neg PA194PAeq.language (peq (^#(1 : V)) s) ^⋎
        (neg PA194PAeq.language (peq (^#(0 : V)) s) ^⋎ peq (^#(1 : V)) (^#(0 : V)))) :=
    IsSemiformula.or.mpr ⟨ha,hbc⟩
  have hin : IsSemiformula PA194PAeq.language 1 (^∀
      (neg PA194PAeq.language (peq (^#(1 : V)) s) ^⋎
        (neg PA194PAeq.language (peq (^#(0 : V)) s) ^⋎ peq (^#(1 : V)) (^#(0 : V))))) :=
    IsSemiformula.all.mpr (by simpa [one_add_one_eq_two] using hq)
  have l1 : s < (^∀ (neg PA194PAeq.language (peq (^#(1 : V)) s) ^⋎
      (neg PA194PAeq.language (peq (^#(0 : V)) s) ^⋎ peq (^#(1 : V)) (^#(0 : V))))) + 1 :=
    lt_trans (lt_trans (lt_trans (lt_npeq_right _ _ (by simp) hs.isUTerm) (lt_qqOr_left _ _))
      (lt_qqAll _)) (lt_add_one _)
  unfold uniq
  rw [termBShift_closed s hs, termBShift_closed s hs, tr_all hin]
  unfold trBody
  rw [translate_all _ _ hq.isUFormula, translate_or _ _ _ ha.isUFormula hbc.isUFormula,
    translate_or _ _ _ hb.isUFormula hc.isUFormula, tf_neg_peq _ _ _ (by simp) hs.isUTerm,
    tf_neg_peq _ _ _ (by simp) hs.isUTerm, atom_two_outer hs l1, atom_two_inner hs l1,
    atom_two_vars]
  rfl

#print axioms termBShift_closed
#print axioms atom_one
#print axioms atom_two_vars
#print axioms tr_nameAll
#print axioms tr_exName
#print axioms tr_uniq
end generic
end PA194GuardedCompiler
