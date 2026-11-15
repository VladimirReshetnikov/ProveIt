import PA194TermNames
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Value formulas of terms

`valBody s` is the source formula of arity one saying that its bound variable is a value of
the arithmetic term `s` of arity zero. The translation of an equality atom and the value
formula of a function term are written here in terms of the value formulas of the arguments,
which the later first-order arguments treat as parameters.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The free environment sends every index to the free variable of that index. -/
def FreeId (P : V) : Prop := ∀ i < len (nth P 1), nth (nth P 1) i = ^&i

theorem FreeId.step {k n P r : V} (hP : ParametersValid k n P) (h : FreeId P) :
    FreeId (parameters (shiftTerms (nth P 0)) (shiftTerms (nth P 1)) r) := by
  intro i hi
  simp only [parameters_free] at hi ⊢
  rw [shiftTerms_length hP.2.1] at hi
  rw [shiftTerms_nth hP.2.1 hi, h i hi, termBShift_fvar]
theorem FreeId.child {k n P : V} (hP : ParametersValid k n P) (h : FreeId P) :
    FreeId (childParameters P) := h.step (r := ^#(0 : V)) hP
theorem FreeId.binary {k n P : V} (j : V) (hP : ParametersValid k n P) (h : FreeId P) :
    FreeId (binaryParameters P j) := by
  have h1 : FreeId (childParameters P) := h.child hP
  have h2 := FreeId.step (r := ^#j) (childParameters_valid hP) h1
  simpa [childParameters, binaryParameters] using h2
theorem idParam_freeId (L : V) : FreeId (idParam L) := (idParam_identity L).2

theorem child_free_len {k n P : V} (hP : ParametersValid k n P) :
    len (nth (childParameters P) 1) = len (nth P 1) := by
  simp [childParameters, shiftTerms_length hP.2.1]
theorem binary_free_len {k n P : V} (j : V) (hP : ParametersValid k n P) :
    len (nth (binaryParameters P j) 1) = len (nth P 1) := by
  have hf := shiftTerms_valid hP.2.1
  simp [binaryParameters, shiftTerms_length hP.2.1, shiftTerms_length hf]

/-- The value formula of a term of arity zero: its bound variable is a value of the term. -/
noncomputable def valBody (s : V) : V := translate (childParameters (idParam (s+1))) s

theorem valBody_valid {s : V} (hs : IsSemiterm PA194PAeq.language 0 s) :
    IsSemiformula SourceL 1 (valBody s) := by
  have hc : ParametersValid 0 1 (childParameters (idParam (s+1))) := by
    simpa using childParameters_valid (idParam_identity (s+1)).1
  exact scope_translate hs.isUTerm 0 1 _ hs hc
    (by rw [child_free_len (idParam_identity (s+1)).1]; simp)

/-- Under any packet whose free environment is the identity, the translation of a term of
arity zero is its value formula at the result term of the packet. -/
theorem translate_lift {k n P s : V} (hP : ParametersValid k n P) (hfree : FreeId P)
    (hs : IsSemiterm PA194PAeq.language 0 s) (hlen : s < len (nth P 1)) :
    translate P s = substs1 SourceL (nth P 2) (valBody s) := by
  have hid := idParam_identity (s + 1 : V)
  have hQ : ParametersValid 0 1 (childParameters (idParam (s+1))) := by
    simpa using childParameters_valid hid.1
  have hQfree : FreeId (childParameters (idParam (s+1))) := (idParam_freeId _).child hid.1
  have hQlen : len (nth (childParameters (idParam (s+1))) 1) = s + 1 := by
    rw [child_free_len hid.1]; simp
  have hw : IsSemitermVec PA194PAeq.language 0 k (0 : V) := by simp
  have hW : IsSemitermVec SourceL 1 n (?[nth P 2] : V) := by simp [hP.2.2]
  have hrel : SubstRel k 0 P (childParameters (idParam (s+1))) (0 : V) (?[nth P 2] : V) := by
    refine ⟨⟨fun i hi => by simp at hi,?_⟩,?_⟩
    · intro i hi
      rw [hQlen] at hi
      have hiP : i < len (nth P 1) := lt_of_le_of_lt (le_iff_lt_succ.mpr hi) hlen
      refine ⟨hiP,?_⟩
      rw [hfree i hiP, hQfree i (by rw [hQlen]; exact hi), termSubst_fvar]
    · simp [childParameters]
  have h := term_subst hs.isUTerm k 0 n 1 P (childParameters (idParam (s+1))) (0 : V)
    (?[nth P 2] : V) hs hw hW hP hQ hrel (by rw [hQlen]; simp)
    (by rw [substs_nil hs]; exact hlen)
  rw [substs_nil hs] at h
  exact h

theorem valBody_shift {s : V} (hs : IsSemiterm PA194PAeq.language 0 s) :
    valBody (termShift PA194PAeq.language s) = shift SourceL (valBody s) := by
  have hid := idParam_identity (s + termShift PA194PAeq.language s + 1 : V)
  have hc : ParametersValid 0 1
      (childParameters (idParam (s + termShift PA194PAeq.language s + 1))) := by
    simpa using childParameters_valid hid.1
  have hfree : FreeId (childParameters (idParam (s + termShift PA194PAeq.language s + 1))) :=
    (idParam_freeId _).child hid.1
  have hl1 : s < len (nth (childParameters (idParam (s + termShift PA194PAeq.language s + 1))) 1) := by
    rw [child_free_len hid.1]
    simpa using lt_succ_of_le' (le_self_add (a := s) (b := termShift PA194PAeq.language s))
  have hl2 : termShift PA194PAeq.language s <
      len (nth (childParameters (idParam (s + termShift PA194PAeq.language s + 1))) 1) := by
    rw [child_free_len hid.1]
    simpa using lt_succ_of_le' (le_add_self (a := termShift PA194PAeq.language s) (b := s))
  have h := term_shift hs.isUTerm 0 1 _ _ hs hc hc (hid.envShiftRel.child hid.1 hid.1) hl1 hl2
  rw [translate_lift hc hfree hs.termShift hl2, translate_lift hc hfree hs hl1] at h
  have hres : nth (childParameters (idParam (s + termShift PA194PAeq.language s + 1))) 2 =
      ^#(0 : V) := by simp [childParameters]
  rw [hres] at h
  have e1 : ∀ X : V, IsSemiformula SourceL 1 X → substs1 SourceL (^#(0 : V)) X = X := by
    intro X hX
    show subst SourceL (?[^#(0 : V)] : V) X = X
    exact subst_eq_self hX (by simp) (fun i hi => by have h0 : i = 0 := (by simpa using hi); subst h0; simp)
  rw [e1 _ (valBody_valid hs.termShift), e1 _ (valBody_valid hs)] at h
  exact h

/-! ### Unfolding -/

theorem tr_peq {s s' : V} (hs : IsSemiterm PA194PAeq.language 0 s)
    (hs' : IsSemiterm PA194PAeq.language 0 s') :
    tr (peq s s') = ^∃ (^∃ (substs1 SourceL (^#(1 : V)) (valBody s) ^⋏
      (substs1 SourceL (^#(0 : V)) (valBody s') ^⋏ orderIsoCode (^#(1 : V)) (^#(0 : V))))) := by
  have hid := idParam_identity (peq s s' + 1 : V)
  have hv : IsUTermVec PA194PAeq.language 2 (?[s,s'] : V) := by simp [hs.isUTerm,hs'.isUTerm]
  have hlt : s < peq s s' := by
    unfold peq
    simpa using (nth_lt_qqRel_of_lt (k := (2 : V)) (r := (0 : V)) (v := (?[s,s'] : V))
      (i := (0 : V)) (by simp))
  have hlt' : s' < peq s s' := by
    unfold peq
    simpa using (nth_lt_qqRel_of_lt (k := (2 : V)) (r := (0 : V)) (v := (?[s,s'] : V))
      (i := (1 : V)) (by simp))
  have hp1 : ParametersValid 0 ((0+1)+1) (binaryParameters (idParam (peq s s' + 1)) 1) :=
    binaryParameters_valid hid.1 (by simp)
  have hp0 : ParametersValid 0 ((0+1)+1) (binaryParameters (idParam (peq s s' + 1)) 0) :=
    binaryParameters_valid hid.1 (by simp)
  have hl1 : s < len (nth (binaryParameters (idParam (peq s s' + 1)) 1) 1) := by
    rw [binary_free_len 1 hid.1]
    simpa using lt_trans hlt (lt_add_one _)
  have hl0 : s' < len (nth (binaryParameters (idParam (peq s s' + 1)) 0) 1) := by
    rw [binary_free_len 0 hid.1]
    simpa using lt_trans hlt' (lt_add_one _)
  have h1 := translate_lift hp1 ((idParam_freeId _).binary 1 hid.1) hs hl1
  have h0 := translate_lift hp0 ((idParam_freeId _).binary 0 hid.1) hs' hl0
  have hr1 : nth (binaryParameters (idParam (peq s s' + 1)) 1) 2 = ^#(1 : V) := by
    simp [binaryParameters]
  have hr0 : nth (binaryParameters (idParam (peq s s' + 1)) 0) 2 = ^#(0 : V) := by
    simp [binaryParameters]
  rw [hr1] at h1
  rw [hr0] at h0
  have h := translate_rel (idParam (peq s s' + 1)) (2 : V) 0 (?[s,s'] : V) isRel_eq hv
  have hn0 : nth (?[s,s'] : V) 0 = s := by simp
  have hn1 : nth (?[s,s'] : V) 1 = s' := by simp
  rw [hn0, hn1] at h
  unfold atomicEquality at h
  rw [h1, h0] at h
  exact h

theorem valBody_fvar (i : V) : valBody (^&i : V) = variableValue (^#(0 : V)) (^&i) := by
  have hid := idParam_identity ((^&i : V) + 1)
  have hi : i < len (nth (childParameters (idParam ((^&i : V) + 1))) 1) := by
    rw [child_free_len hid.1]
    simpa using lt_trans (lt_qqFvar i) (lt_add_one _)
  unfold valBody
  rw [translate_free, ((idParam_freeId _).child hid.1) i hi]
  simp [childParameters]
theorem valBody_zero : valBody (zeroT : V) = zeroValue (^#(0 : V)) := by
  unfold valBody zeroT
  rw [translate_zero]
  simp [childParameters]
theorem valBody_succ {s : V} (hs : IsSemiterm PA194PAeq.language 0 s) :
    valBody (succT s) = successorValue (^#(0 : V)) (substs1 SourceL (^#(0 : V)) (valBody s)) := by
  have hid := idParam_identity (succT s + 1 : V)
  have hc : ParametersValid 0 1 (childParameters (idParam (succT s + 1))) := by
    simpa using childParameters_valid hid.1
  have hcc : ParametersValid 0 (1+1) (childParameters (childParameters (idParam (succT s + 1)))) :=
    childParameters_valid hc
  have hlt : s < succT s := by
    unfold succT
    simpa using (nth_lt_qqFunc_of_lt (k := (1 : V)) (f := (1 : V)) (v := (?[s] : V))
      (i := (0 : V)) (by simp))
  have hl : s < len (nth (childParameters (childParameters (idParam (succT s + 1)))) 1) := by
    rw [child_free_len hc, child_free_len hid.1]
    simpa using lt_trans hlt (lt_add_one _)
  have h1 := translate_lift hcc (((idParam_freeId _).child hid.1).child hc) hs hl
  have hr : nth (childParameters (childParameters (idParam (succT s + 1)))) 2 = ^#(0 : V) := by
    simp [childParameters]
  rw [hr] at h1
  have h := translate_succ (childParameters (idParam (succT s + 1))) s hs.isUTerm
  rw [h1] at h
  have hr' : nth (childParameters (idParam (succT s + 1))) 2 = ^#(0 : V) := by
    simp [childParameters]
  rw [hr'] at h
  exact h
theorem valBody_add {s s' : V} (hs : IsSemiterm PA194PAeq.language 0 s)
    (hs' : IsSemiterm PA194PAeq.language 0 s') :
    valBody (addT s s') = binaryValue additionTemplate (^#(0 : V))
      (substs1 SourceL (^#(1 : V)) (valBody s)) (substs1 SourceL (^#(0 : V)) (valBody s')) := by
  have hid := idParam_identity (addT s s' + 1 : V)
  have hc : ParametersValid 0 1 (childParameters (idParam (addT s s' + 1))) := by
    simpa using childParameters_valid hid.1
  have hfc : FreeId (childParameters (idParam (addT s s' + 1))) := (idParam_freeId _).child hid.1
  have hlt : s < addT s s' := by
    unfold addT
    simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := (2 : V)) (v := (?[s,s'] : V))
      (i := (0 : V)) (by simp))
  have hlt' : s' < addT s s' := by
    unfold addT
    simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := (2 : V)) (v := (?[s,s'] : V))
      (i := (1 : V)) (by simp))
  have hp1 := binaryParameters_valid (i := (1 : V)) hc (by simp)
  have hp0 := binaryParameters_valid (i := (0 : V)) hc (by simp)
  have hl1 : s < len (nth (binaryParameters (childParameters (idParam (addT s s' + 1))) 1) 1) := by
    rw [binary_free_len 1 hc, child_free_len hid.1]
    simpa using lt_trans hlt (lt_add_one _)
  have hl0 : s' < len (nth (binaryParameters (childParameters (idParam (addT s s' + 1))) 0) 1) := by
    rw [binary_free_len 0 hc, child_free_len hid.1]
    simpa using lt_trans hlt' (lt_add_one _)
  have h1 := translate_lift hp1 (hfc.binary 1 hc) hs hl1
  have h0 := translate_lift hp0 (hfc.binary 0 hc) hs' hl0
  have hr1 : nth (binaryParameters (childParameters (idParam (addT s s' + 1))) 1) 2 = ^#(1 : V) := by
    simp [binaryParameters]
  have hr0 : nth (binaryParameters (childParameters (idParam (addT s s' + 1))) 0) 2 = ^#(0 : V) := by
    simp [binaryParameters]
  rw [hr1] at h1
  rw [hr0] at h0
  have h := translate_add (childParameters (idParam (addT s s' + 1))) s s' hs.isUTerm hs'.isUTerm
  rw [h1, h0] at h
  have hr' : nth (childParameters (idParam (addT s s' + 1))) 2 = ^#(0 : V) := by
    simp [childParameters]
  rw [hr'] at h
  exact h
theorem valBody_mul {s s' : V} (hs : IsSemiterm PA194PAeq.language 0 s)
    (hs' : IsSemiterm PA194PAeq.language 0 s') :
    valBody (mulT s s') = binaryValue multiplicationTemplate (^#(0 : V))
      (substs1 SourceL (^#(1 : V)) (valBody s)) (substs1 SourceL (^#(0 : V)) (valBody s')) := by
  have hid := idParam_identity (mulT s s' + 1 : V)
  have hc : ParametersValid 0 1 (childParameters (idParam (mulT s s' + 1))) := by
    simpa using childParameters_valid hid.1
  have hfc : FreeId (childParameters (idParam (mulT s s' + 1))) := (idParam_freeId _).child hid.1
  have hlt : s < mulT s s' := by
    unfold mulT
    simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := (3 : V)) (v := (?[s,s'] : V))
      (i := (0 : V)) (by simp))
  have hlt' : s' < mulT s s' := by
    unfold mulT
    simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := (3 : V)) (v := (?[s,s'] : V))
      (i := (1 : V)) (by simp))
  have hp1 := binaryParameters_valid (i := (1 : V)) hc (by simp)
  have hp0 := binaryParameters_valid (i := (0 : V)) hc (by simp)
  have hl1 : s < len (nth (binaryParameters (childParameters (idParam (mulT s s' + 1))) 1) 1) := by
    rw [binary_free_len 1 hc, child_free_len hid.1]
    simpa using lt_trans hlt (lt_add_one _)
  have hl0 : s' < len (nth (binaryParameters (childParameters (idParam (mulT s s' + 1))) 0) 1) := by
    rw [binary_free_len 0 hc, child_free_len hid.1]
    simpa using lt_trans hlt' (lt_add_one _)
  have h1 := translate_lift hp1 (hfc.binary 1 hc) hs hl1
  have h0 := translate_lift hp0 (hfc.binary 0 hc) hs' hl0
  have hr1 : nth (binaryParameters (childParameters (idParam (mulT s s' + 1))) 1) 2 = ^#(1 : V) := by
    simp [binaryParameters]
  have hr0 : nth (binaryParameters (childParameters (idParam (mulT s s' + 1))) 0) 2 = ^#(0 : V) := by
    simp [binaryParameters]
  rw [hr1] at h1
  rw [hr0] at h0
  have h := translate_mul (childParameters (idParam (mulT s s' + 1))) s s' hs.isUTerm hs'.isUTerm
  rw [h1, h0] at h
  have hr' : nth (childParameters (idParam (mulT s s' + 1))) 2 = ^#(0 : V) := by
    simp [childParameters]
  rw [hr'] at h
  exact h

#print axioms translate_lift
#print axioms valBody_shift
#print axioms tr_peq
#print axioms valBody_succ
#print axioms valBody_add
#print axioms valBody_mul
end generic
end PA194GuardedCompiler
