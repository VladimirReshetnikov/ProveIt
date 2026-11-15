import PA194TranslateShift
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The translation commutes with the substitution of variables

A substitution of the arithmetic language whose entries are variables corresponds to a
substitution of the source language applied to the translation, when the packets are related
accordingly. With the shift lemma this gives the translation of `free p`, and from it the
universal rule of the guarded compiler.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher
open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Quantifier vectors -/

theorem qVec_nth_zero (W : V) : nth (qVec SourceL W) 0 = ^#(0 : V) := by
  simp [qVec]
theorem qVec_nth_succ {k n W i : V} (hW : IsSemitermVec SourceL k n W) (hi : i < k) :
    nth (qVec SourceL W) (i+1) = termBShift SourceL (nth W i) := by
  have hl : len W = k := hW.isUTerm.lh.symm
  unfold qVec
  rw [nth_adjoin_succ, hl, nth_termBShiftVec hW.isUTerm hi]
theorem qVec_qVec_nth_one {n m W : V} (hW : IsSemitermVec SourceL n m W) :
    nth (qVec SourceL (qVec SourceL W)) 1 = ^#(1 : V) := by
  have h := qVec_nth_succ hW.qVec (i := 0) (by simp)
  simpa [qVec_nth_zero] using h
theorem qVecA_nth_zero (w : V) : nth (qVec PA194PAeq.language w) 0 = ^#(0 : V) := by
  simp [qVec]
theorem qVecA_nth_succ {k n w i : V} (hw : IsSemitermVec PA194PAeq.language k n w) (hi : i < k) :
    nth (qVec PA194PAeq.language w) (i+1) = termBShift PA194PAeq.language (nth w i) := by
  have hl : len w = k := hw.isUTerm.lh.symm
  unfold qVec
  rw [nth_adjoin_succ, hl, nth_termBShiftVec hw.isUTerm hi]

/-! ### Templates under substitution -/

theorem templateOne_subst (p : Semiproposition SourceL 1) {n m z W : V}
    (hz : IsSemiterm SourceL n z) (hW : IsSemitermVec SourceL n m W) :
    subst SourceL W (templateOne p z) = templateOne p (termSubst SourceL W z) := by
  have hq : IsSemiformula SourceL 1 (⌜p⌝ : V) := by
    simp
  have hv : IsSemitermVec SourceL 1 n (?[z] : V) := by simp [hz]
  show subst SourceL W (subst SourceL (?[z] : V) ⌜p⌝) =
    subst SourceL (?[termSubst SourceL W z] : V) ⌜p⌝
  rw [substs_substs hq hW hv, termSubstVec_cons₁ hz.isUTerm]
theorem templateTwo_subst (p : Semiproposition SourceL 2) {n m x z W : V}
    (hx : IsSemiterm SourceL n x) (hz : IsSemiterm SourceL n z) (hW : IsSemitermVec SourceL n m W) :
    subst SourceL W (templateTwo p x z) =
      templateTwo p (termSubst SourceL W x) (termSubst SourceL W z) := by
  have hq : IsSemiformula SourceL 2 (⌜p⌝ : V) := by
    simpa using Semiformula.quote_isSemiformula (V := V) p
  have hv : IsSemitermVec SourceL 2 n (?[x,z] : V) := by simp [hx,hz]
  show subst SourceL W (subst SourceL (?[x,z] : V) ⌜p⌝) =
    subst SourceL (?[termSubst SourceL W x,termSubst SourceL W z] : V) ⌜p⌝
  rw [substs_substs hq hW hv, termSubstVec_cons₂ hx.isUTerm hz.isUTerm]
theorem templateThree_subst (p : Semiproposition SourceL 3) {n m x y z W : V}
    (hx : IsSemiterm SourceL n x) (hy : IsSemiterm SourceL n y) (hz : IsSemiterm SourceL n z)
    (hW : IsSemitermVec SourceL n m W) :
    subst SourceL W (templateThree p x y z) =
      templateThree p (termSubst SourceL W x) (termSubst SourceL W y) (termSubst SourceL W z) := by
  have hq : IsSemiformula SourceL 3 (⌜p⌝ : V) := by
    simpa using Semiformula.quote_isSemiformula (V := V) p
  have hv : IsSemitermVec SourceL 3 n (?[x,y,z] : V) := by
    simp [hx,hy,hz,show (3:V)=2+1 from two_add_one_eq_three.symm]
  have hyz : IsUTermVec SourceL 2 (?[y,z] : V) := by simp [hy.isUTerm,hz.isUTerm]
  have h3 : termSubstVec SourceL 3 W (?[x,y,z] : V) =
      ?[termSubst SourceL W x,termSubst SourceL W y,termSubst SourceL W z] := by
    rw [show (3:V)=2+1 from two_add_one_eq_three.symm, termSubstVec_cons hx.isUTerm hyz,
      termSubstVec_cons₂ hy.isUTerm hz.isUTerm]
  show subst SourceL W (subst SourceL (?[x,y,z] : V) ⌜p⌝) =
    subst SourceL (?[termSubst SourceL W x,termSubst SourceL W y,termSubst SourceL W z] : V) ⌜p⌝
  rw [substs_substs hq hW hv, h3]

theorem domainCode_subst {n m z W : V} (hz : IsSemiterm SourceL n z)
    (hW : IsSemitermVec SourceL n m W) :
    subst SourceL W (domainCode z) = domainCode (termSubst SourceL W z) :=
  templateOne_subst domainTemplate hz hW
theorem zeroCode_subst {n m z W : V} (hz : IsSemiterm SourceL n z)
    (hW : IsSemitermVec SourceL n m W) :
    subst SourceL W (zeroCode z) = zeroCode (termSubst SourceL W z) :=
  templateOne_subst zeroTemplate hz hW
theorem equalityCode_subst {n m x z W : V} (hx : IsSemiterm SourceL n x)
    (hz : IsSemiterm SourceL n z) (hW : IsSemitermVec SourceL n m W) :
    subst SourceL W (equalityCode x z) =
      equalityCode (termSubst SourceL W x) (termSubst SourceL W z) :=
  templateTwo_subst equalityTemplate hx hz hW
theorem successorCode_subst {n m x z W : V} (hx : IsSemiterm SourceL n x)
    (hz : IsSemiterm SourceL n z) (hW : IsSemitermVec SourceL n m W) :
    subst SourceL W (successorCode x z) =
      successorCode (termSubst SourceL W x) (termSubst SourceL W z) :=
  templateTwo_subst successorTemplate hx hz hW
theorem orderIsoCode_subst {n m x z W : V} (hx : IsSemiterm SourceL n x)
    (hz : IsSemiterm SourceL n z) (hW : IsSemitermVec SourceL n m W) :
    subst SourceL W (orderIsoCode x z) =
      orderIsoCode (termSubst SourceL W x) (termSubst SourceL W z) :=
  templateTwo_subst orderIsoTemplate hx hz hW

/-! ### Value constructors -/

theorem variableValue_subst {n m z x W : V} (hz : IsSemiterm SourceL n z)
    (hx : IsSemiterm SourceL n x) (hW : IsSemitermVec SourceL n m W) :
    subst SourceL W (variableValue z x) =
      variableValue (termSubst SourceL W z) (termSubst SourceL W x) := by
  unfold variableValue
  rw [substs_and (domainCode_valid hz).isUFormula (equalityCode_valid hz hx).isUFormula,
    domainCode_subst hz hW, equalityCode_subst hz hx hW]
theorem zeroValue_subst {n m z W : V} (hz : IsSemiterm SourceL n z)
    (hW : IsSemitermVec SourceL n m W) :
    subst SourceL W (zeroValue z) = zeroValue (termSubst SourceL W z) := by
  unfold zeroValue
  rw [substs_and (domainCode_valid hz).isUFormula (zeroCode_valid hz).isUFormula,
    domainCode_subst hz hW, zeroCode_subst hz hW]
theorem successorValue_subst {n m z c W : V} (hz : IsSemiterm SourceL n z)
    (hc : IsSemiformula SourceL (n+1) c) (hW : IsSemitermVec SourceL n m W) :
    subst SourceL W (successorValue z c) =
      successorValue (termSubst SourceL W z) (subst SourceL (qVec SourceL W) c) := by
  have hb : IsSemiterm SourceL (n+1) (termBShift SourceL z) := IsSemiterm.termBShift hz
  have h0 : IsSemiterm SourceL (n+1) (^#(0 : V)) := by simp
  have hs : IsSemiformula SourceL (n+1) (successorCode (^#(0 : V)) (termBShift SourceL z)) :=
    successorCode_valid h0 hb
  have hcs := IsSemiformula.and.mpr ⟨hc,hs⟩
  have he : IsSemiformula SourceL n (^∃ (c ^⋏ successorCode (^#(0 : V)) (termBShift SourceL z))) :=
    IsSemiformula.exs.mpr hcs
  unfold successorValue
  rw [substs_and (domainCode_valid hz).isUFormula he.isUFormula, substs_ex hcs.isUFormula,
    substs_and hc.isUFormula hs.isUFormula, domainCode_subst hz hW,
    successorCode_subst h0 hb hW.qVec, termSubst_bvar, qVec_nth_zero, substs_qVec_bShift hz hW]
theorem binaryValue_subst (p : Semiproposition SourceL 3) {n m z l r W : V}
    (hz : IsSemiterm SourceL n z) (hl : IsSemiformula SourceL ((n+1)+1) l)
    (hr : IsSemiformula SourceL ((n+1)+1) r) (hW : IsSemitermVec SourceL n m W) :
    subst SourceL W (binaryValue p z l r) =
      binaryValue p (termSubst SourceL W z) (subst SourceL (qVec SourceL (qVec SourceL W)) l)
        (subst SourceL (qVec SourceL (qVec SourceL W)) r) := by
  have hb1 : IsSemiterm SourceL (n+1) (termBShift SourceL z) := IsSemiterm.termBShift hz
  have hb : IsSemiterm SourceL ((n+1)+1) (termBShift SourceL (termBShift SourceL z)) :=
    IsSemiterm.termBShift hb1
  have h1 : IsSemiterm SourceL ((n+1)+1) (^#(1 : V)) := by simp
  have h0 : IsSemiterm SourceL ((n+1)+1) (^#(0 : V)) := by simp
  have ht : IsSemiformula SourceL ((n+1)+1)
      (templateThree p (^#(1 : V)) (^#(0 : V)) (termBShift SourceL (termBShift SourceL z))) :=
    templateThree_valid p h1 h0 hb
  have hrt := IsSemiformula.and.mpr ⟨hr,ht⟩
  have hlrt := IsSemiformula.and.mpr ⟨hl,hrt⟩
  have he1 : IsSemiformula SourceL (n+1) (^∃ (l ^⋏ (r ^⋏
      templateThree p (^#(1 : V)) (^#(0 : V)) (termBShift SourceL (termBShift SourceL z))))) :=
    IsSemiformula.exs.mpr hlrt
  have he2 : IsSemiformula SourceL n (^∃ (^∃ (l ^⋏ (r ^⋏
      templateThree p (^#(1 : V)) (^#(0 : V)) (termBShift SourceL (termBShift SourceL z)))))) :=
    IsSemiformula.exs.mpr he1
  unfold binaryValue
  rw [substs_and (domainCode_valid hz).isUFormula he2.isUFormula, substs_ex he1.isUFormula,
    substs_ex hlrt.isUFormula, substs_and hl.isUFormula hrt.isUFormula,
    substs_and hr.isUFormula ht.isUFormula, domainCode_subst hz hW,
    templateThree_subst p h1 h0 hb hW.qVec.qVec, termSubst_bvar, termSubst_bvar,
    qVec_qVec_nth_one hW, qVec_nth_zero, substs_qVec_bShift hb1 hW.qVec, substs_qVec_bShift hz hW]
theorem equalityOutput_subst {n m l r W : V} (hl : IsSemiformula SourceL ((n+1)+1) l)
    (hr : IsSemiformula SourceL ((n+1)+1) r) (hW : IsSemitermVec SourceL n m W) :
    subst SourceL W (^∃ (^∃ (l ^⋏ (r ^⋏ orderIsoCode (^#(1 : V)) (^#(0 : V)))))) =
      ^∃ (^∃ (subst SourceL (qVec SourceL (qVec SourceL W)) l ^⋏
        (subst SourceL (qVec SourceL (qVec SourceL W)) r ^⋏ orderIsoCode (^#(1 : V)) (^#(0 : V))))) := by
  have h1 : IsSemiterm SourceL ((n+1)+1) (^#(1 : V)) := by simp
  have h0 : IsSemiterm SourceL ((n+1)+1) (^#(0 : V)) := by simp
  have ho : IsSemiformula SourceL ((n+1)+1) (orderIsoCode (^#(1 : V)) (^#(0 : V))) :=
    templateTwo_valid orderIsoTemplate h1 h0
  have hro := IsSemiformula.and.mpr ⟨hr,ho⟩
  have hlro := IsSemiformula.and.mpr ⟨hl,hro⟩
  have he : IsSemiformula SourceL (n+1)
      (^∃ (l ^⋏ (r ^⋏ orderIsoCode (^#(1 : V)) (^#(0 : V))))) := IsSemiformula.exs.mpr hlro
  rw [substs_ex he.isUFormula, substs_ex hlro.isUFormula, substs_and hl.isUFormula hro.isUFormula,
    substs_and hr.isUFormula ho.isUFormula, orderIsoCode_subst h1 h0 hW.qVec.qVec,
    termSubst_bvar, termSubst_bvar, qVec_qVec_nth_one hW, qVec_nth_zero]
theorem allOutput_subst {n m c W : V} (hc : IsSemiformula SourceL (n+1) c)
    (hW : IsSemitermVec SourceL n m W) :
    subst SourceL W (allOutput c) = allOutput (subst SourceL (qVec SourceL W) c) := by
  have h0 : IsSemiterm SourceL (n+1) (^#(0 : V)) := by simp
  have hd : IsSemiformula SourceL (n+1) (domainCode (^#(0 : V))) := domainCode_valid h0
  have hnd : IsSemiformula SourceL (n+1) (neg SourceL (domainCode (^#(0 : V)))) :=
    IsSemiformula.neg_iff.mpr hd
  have himp : IsSemiformula SourceL (n+1) (neg SourceL (domainCode (^#(0 : V))) ^⋎ c) :=
    IsSemiformula.or.mpr ⟨hnd,hc⟩
  show subst SourceL W (^∀ (neg SourceL (domainCode (^#(0 : V))) ^⋎ c)) =
    ^∀ (neg SourceL (domainCode (^#(0 : V))) ^⋎ subst SourceL (qVec SourceL W) c)
  rw [substs_all himp.isUFormula, substs_or hnd.isUFormula hc.isUFormula, substs_neg hd hW.qVec,
    domainCode_subst h0 hW.qVec, termSubst_bvar, qVec_nth_zero]
theorem exsOutput_subst {n m c W : V} (hc : IsSemiformula SourceL (n+1) c)
    (hW : IsSemitermVec SourceL n m W) :
    subst SourceL W (exsOutput c) = exsOutput (subst SourceL (qVec SourceL W) c) := by
  have h0 : IsSemiterm SourceL (n+1) (^#(0 : V)) := by simp
  have hd : IsSemiformula SourceL (n+1) (domainCode (^#(0 : V))) := domainCode_valid h0
  have hand := IsSemiformula.and.mpr ⟨hd,hc⟩
  unfold exsOutput
  rw [substs_ex hand.isUFormula, substs_and hd.isUFormula hc.isUFormula,
    domainCode_subst h0 hW.qVec, termSubst_bvar, qVec_nth_zero]

/-! ### Packets related by a substitution of variables -/

/-- `P` reads the variable `w.[i]` where `Q` reads the bound variable `i`, up to `W`. -/
def EnvSubstRel (s s' P Q w W : V) : Prop :=
  (∀ i < s',
    (∃ j < s, nth w i = ^#j ∧ nth (nth P 0) j = termSubst SourceL W (nth (nth Q 0) i)) ∨
    (∃ j < len (nth P 1), nth w i = ^&j ∧ nth (nth P 1) j = termSubst SourceL W (nth (nth Q 0) i))) ∧
  (∀ i < len (nth Q 1), i < len (nth P 1) ∧
    nth (nth P 1) i = termSubst SourceL W (nth (nth Q 1) i))
def SubstRel (s s' P Q w W : V) : Prop :=
  EnvSubstRel s s' P Q w W ∧ nth P 2 = termSubst SourceL W (nth Q 2)

theorem EnvSubstRel.step {s s' n n' P Q w W rP rQ : V} (hP : ParametersValid s n P)
    (hQ : ParametersValid s' n' Q) (hW : IsSemitermVec SourceL n' n W)
    (h : EnvSubstRel s s' P Q w W) (hr : rP = termSubst SourceL (qVec SourceL W) rQ) :
    SubstRel s s' (parameters (shiftTerms (nth P 0)) (shiftTerms (nth P 1)) rP)
      (parameters (shiftTerms (nth Q 0)) (shiftTerms (nth Q 1)) rQ) w (qVec SourceL W) := by
  simp only [SubstRel, EnvSubstRel, parameters_bound, parameters_free, parameters_result]
  refine ⟨⟨?_,?_⟩,hr⟩
  · intro i hi
    rcases h.1 i hi with ⟨j,hj,hw,he⟩ | ⟨j,hj,hw,he⟩
    · refine Or.inl ⟨j,hj,hw,?_⟩
      rw [shiftTerms_nth hP.1 hj, shiftTerms_nth hQ.1 hi, he, substs_qVec_bShift (hQ.1.nth hi) hW]
    · refine Or.inr ⟨j,by rw [shiftTerms_length hP.2.1]; exact hj,hw,?_⟩
      rw [shiftTerms_nth hP.2.1 hj, shiftTerms_nth hQ.1 hi, he, substs_qVec_bShift (hQ.1.nth hi) hW]
  · intro i hi
    rw [shiftTerms_length hQ.2.1] at hi
    obtain ⟨hi',he⟩ := h.2 i hi
    refine ⟨by rw [shiftTerms_length hP.2.1]; exact hi',?_⟩
    rw [shiftTerms_nth hP.2.1 hi', shiftTerms_nth hQ.2.1 hi, he,
      substs_qVec_bShift (hQ.2.1.nth hi) hW]
theorem EnvSubstRel.child {s s' n n' P Q w W : V} (hP : ParametersValid s n P)
    (hQ : ParametersValid s' n' Q) (hW : IsSemitermVec SourceL n' n W)
    (h : EnvSubstRel s s' P Q w W) :
    SubstRel s s' (childParameters P) (childParameters Q) w (qVec SourceL W) :=
  h.step hP hQ hW (rP := ^#(0 : V)) (rQ := ^#(0 : V)) (by rw [termSubst_bvar, qVec_nth_zero])
theorem EnvSubstRel.binaryOne {s s' n n' P Q w W : V} (hP : ParametersValid s n P)
    (hQ : ParametersValid s' n' Q) (hW : IsSemitermVec SourceL n' n W)
    (h : EnvSubstRel s s' P Q w W) :
    SubstRel s s' (binaryParameters P 1) (binaryParameters Q 1) w
      (qVec SourceL (qVec SourceL W)) := by
  have h1 : SubstRel s s' (childParameters P) (childParameters Q) w (qVec SourceL W) :=
    h.child hP hQ hW
  have h2 := EnvSubstRel.step (childParameters_valid hP) (childParameters_valid hQ) hW.qVec h1.1
    (rP := ^#(1 : V)) (rQ := ^#(1 : V)) (by rw [termSubst_bvar, qVec_qVec_nth_one hW])
  simpa [childParameters, binaryParameters] using h2
theorem EnvSubstRel.binaryZero {s s' n n' P Q w W : V} (hP : ParametersValid s n P)
    (hQ : ParametersValid s' n' Q) (hW : IsSemitermVec SourceL n' n W)
    (h : EnvSubstRel s s' P Q w W) :
    SubstRel s s' (binaryParameters P 0) (binaryParameters Q 0) w
      (qVec SourceL (qVec SourceL W)) := by
  have h1 : SubstRel s s' (childParameters P) (childParameters Q) w (qVec SourceL W) :=
    h.child hP hQ hW
  have h2 := EnvSubstRel.step (childParameters_valid hP) (childParameters_valid hQ) hW.qVec h1.1
    (rP := ^#(0 : V)) (rQ := ^#(0 : V)) (by rw [termSubst_bvar, qVec_nth_zero])
  simpa [childParameters, binaryParameters] using h2
theorem EnvSubstRel.formulaChild {s s' n n' P Q w W : V} (hP : ParametersValid s n P)
    (hQ : ParametersValid s' n' Q) (hw : IsSemitermVec PA194PAeq.language s' s w)
    (hW : IsSemitermVec SourceL n' n W) (h : EnvSubstRel s s' P Q w W) :
    EnvSubstRel (s+1) (s'+1) (formulaChildParameters P) (formulaChildParameters Q)
      (qVec PA194PAeq.language w) (qVec SourceL W) := by
  simp only [EnvSubstRel, formulaChildParameters, parameters_bound, parameters_free]
  refine ⟨?_,?_⟩
  · intro i hi
    rcases zero_or_succ i with (rfl | ⟨i0,rfl⟩)
    · refine Or.inl ⟨0,by simp,qVecA_nth_zero w,?_⟩
      rw [nth_adjoin_zero, nth_adjoin_zero, termSubst_bvar, qVec_nth_zero]
    · have hi0 : i0 < s' := by simpa using hi
      rw [qVecA_nth_succ hw hi0]
      rcases h.1 i0 hi0 with ⟨j,hj,hwj,he⟩ | ⟨j,hj,hwj,he⟩
      · refine Or.inl ⟨j+1,by simpa using hj,by rw [hwj, termBShift_bvar],?_⟩
        rw [nth_adjoin_succ, nth_adjoin_succ, shiftTerms_nth hP.1 hj, shiftTerms_nth hQ.1 hi0, he,
          substs_qVec_bShift (hQ.1.nth hi0) hW]
      · refine Or.inr ⟨j,by rw [shiftTerms_length hP.2.1]; exact hj,by rw [hwj, termBShift_fvar],?_⟩
        rw [nth_adjoin_succ, shiftTerms_nth hP.2.1 hj, shiftTerms_nth hQ.1 hi0, he,
          substs_qVec_bShift (hQ.1.nth hi0) hW]
  · intro i hi
    rw [shiftTerms_length hQ.2.1] at hi
    obtain ⟨hi',he⟩ := h.2 i hi
    refine ⟨by rw [shiftTerms_length hP.2.1]; exact hi',?_⟩
    rw [shiftTerms_nth hP.2.1 hi', shiftTerms_nth hQ.2.1 hi, he,
      substs_qVec_bShift (hQ.2.1.nth hi) hW]

/-! ### Terms -/

def TermSubstProperty (t : V) : Prop :=
  ∀ s s' n n' P Q w W, IsSemiterm PA194PAeq.language s' t →
    IsSemitermVec PA194PAeq.language s' s w → IsSemitermVec SourceL n' n W →
    ParametersValid s n P → ParametersValid s' n' Q → SubstRel s s' P Q w W →
    t < len (nth Q 1) → termSubst PA194PAeq.language w t < len (nth P 1) →
    translate P (termSubst PA194PAeq.language w t) = subst SourceL W (translate Q t)
theorem TermSubstProperty_definable : 𝚷₁-Predicate (TermSubstProperty : V → Prop) := by
  haveI : 𝚺₁-Function₂ (translate : V → V → V) := translate_defined.to_definable
  unfold TermSubstProperty ParametersValid SubstRel EnvSubstRel
  definability

theorem term_subst {t : V} (ht : IsUTerm PA194PAeq.language t) : TermSubstProperty t := by
  apply IsUTerm.induction 𝚷 TermSubstProperty_definable ?_ ?_ ?_ t ht
  · intro i s s' n n' P Q w W hterm hw hW hP hQ hrel hlen hlen'
    have hi : i < s' := by simpa using hterm
    rw [termSubst_bvar, translate_bound, variableValue_subst hQ.2.2 (hQ.1.nth hi) hW, ← hrel.2]
    rcases hrel.1.1 i hi with ⟨j,hj,hwj,he⟩ | ⟨j,hj,hwj,he⟩
    · rw [hwj, translate_bound, he]
    · rw [hwj, translate_free, he]
  · intro i s s' n n' P Q w W hterm hw hW hP hQ hrel hlen hlen'
    have hi : i < len (nth Q 1) := lt_trans (lt_qqFvar i) hlen
    rw [termSubst_fvar, translate_free, translate_free,
      variableValue_subst hQ.2.2 (hQ.2.1.nth hi) hW, ← hrel.2, ← (hrel.1.2 i hi).2]
  · intro k f v hf hv ih s s' n n' P Q w W hterm hw hW hP hQ hrel hlen hlen'
    have hsv : IsSemitermVec PA194PAeq.language k s' v := ((IsSemiterm.func).mp hterm).2
    rw [termSubst_func hf hv] at hlen' ⊢
    rcases (PA194PAeq.source_functions k f).mp hf with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,htwo⟩
    · have hv0 : v = 0 := len_zero_iff_eq_nil.mp hv.lh.symm
      subst v
      rw [termSubstVec_nil, translate_zero, translate_zero, zeroValue_subst hQ.2.2 hW, hrel.2]
    · obtain ⟨a,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      have ha : IsSemiterm PA194PAeq.language s' a := by
        simpa using hsv.nth (show (0 : V) < 1 by simp)
      have hsa : IsSemiterm PA194PAeq.language s (termSubst PA194PAeq.language w a) :=
        hw.termSubst ha
      rw [termSubstVec_cons₁ ha.isUTerm] at hlen' ⊢
      have hca : a < len (nth Q 1) := lt_trans (by
        simpa using (nth_lt_qqFunc_of_lt (k := (1 : V)) (f := (1 : V)) (v := (?[a] : V))
          (i := (0 : V)) (by simp))) hlen
      have hca' : termSubst PA194PAeq.language w a < len (nth P 1) := lt_trans (by
        simpa using (nth_lt_qqFunc_of_lt (k := (1 : V)) (f := (1 : V))
          (v := (?[termSubst PA194PAeq.language w a] : V)) (i := (0 : V)) (by simp))) hlen'
      have hcp : ParametersValid s (n+1) (childParameters P) := childParameters_valid hP
      have hcq : ParametersValid s' (n'+1) (childParameters Q) := childParameters_valid hQ
      have hl1 : a < len (nth (childParameters Q) 1) := by
        simpa [childParameters, shiftTerms_length hQ.2.1] using hca
      have hl2 : termSubst PA194PAeq.language w a < len (nth (childParameters P) 1) := by
        simpa [childParameters, shiftTerms_length hP.2.1] using hca'
      have hchild : translate (childParameters P) (termSubst PA194PAeq.language w a) =
          subst SourceL (qVec SourceL W) (translate (childParameters Q) a) := by
        simpa using ih 0 (by simp) s s' (n+1) (n'+1) (childParameters P) (childParameters Q) w
          (qVec SourceL W) (by simpa using ha) hw hW.qVec hcp hcq (hrel.1.child hP hQ hW)
          (by simpa using hl1) (by simpa using hl2)
      have hscope := scope_translate ha.isUTerm s' (n'+1) (childParameters Q) ha hcq hl1
      rw [translate_succ P _ hsa.isUTerm, translate_succ Q a ha.isUTerm,
        successorValue_subst hQ.2.2 hscope hW, hrel.2, hchild]
    · obtain ⟨a,b,rfl⟩ := eq_doubleton_of_len_eq_two.mp hv.lh.symm
      have ha : IsSemiterm PA194PAeq.language s' a := by
        simpa using hsv.nth (show (0 : V) < 2 by simp)
      have hb : IsSemiterm PA194PAeq.language s' b := by
        simpa using hsv.nth (show (1 : V) < 2 by simp)
      have hsa : IsSemiterm PA194PAeq.language s (termSubst PA194PAeq.language w a) :=
        hw.termSubst ha
      have hsb : IsSemiterm PA194PAeq.language s (termSubst PA194PAeq.language w b) :=
        hw.termSubst hb
      rw [termSubstVec_cons₂ ha.isUTerm hb.isUTerm] at hlen' ⊢
      have hca : a < len (nth Q 1) := lt_trans (by
        simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := f) (v := (?[a,b] : V))
          (i := (0 : V)) (by simp))) hlen
      have hcb : b < len (nth Q 1) := lt_trans (by
        simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := f) (v := (?[a,b] : V))
          (i := (1 : V)) (by simp))) hlen
      have hca' : termSubst PA194PAeq.language w a < len (nth P 1) := lt_trans (by
        simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := f)
          (v := (?[termSubst PA194PAeq.language w a,termSubst PA194PAeq.language w b] : V))
          (i := (0 : V)) (by simp))) hlen'
      have hcb' : termSubst PA194PAeq.language w b < len (nth P 1) := lt_trans (by
        simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := f)
          (v := (?[termSubst PA194PAeq.language w a,termSubst PA194PAeq.language w b] : V))
          (i := (1 : V)) (by simp))) hlen'
      have hp1 : ParametersValid s ((n+1)+1) (binaryParameters P 1) :=
        binaryParameters_valid hP (by simp)
      have hp0 : ParametersValid s ((n+1)+1) (binaryParameters P 0) :=
        binaryParameters_valid hP (by simp)
      have hq1 : ParametersValid s' ((n'+1)+1) (binaryParameters Q 1) :=
        binaryParameters_valid hQ (by simp)
      have hq0 : ParametersValid s' ((n'+1)+1) (binaryParameters Q 0) :=
        binaryParameters_valid hQ (by simp)
      have hfP := shiftTerms_valid hP.2.1
      have hfQ := shiftTerms_valid hQ.2.1
      have hl1 : a < len (nth (binaryParameters Q 1) 1) := by
        simpa [binaryParameters,shiftTerms_length hQ.2.1,shiftTerms_length hfQ] using hca
      have hl0 : b < len (nth (binaryParameters Q 0) 1) := by
        simpa [binaryParameters,shiftTerms_length hQ.2.1,shiftTerms_length hfQ] using hcb
      have hl1' : termSubst PA194PAeq.language w a < len (nth (binaryParameters P 1) 1) := by
        simpa [binaryParameters,shiftTerms_length hP.2.1,shiftTerms_length hfP] using hca'
      have hl0' : termSubst PA194PAeq.language w b < len (nth (binaryParameters P 0) 1) := by
        simpa [binaryParameters,shiftTerms_length hP.2.1,shiftTerms_length hfP] using hcb'
      have hleft : translate (binaryParameters P 1) (termSubst PA194PAeq.language w a) =
          subst SourceL (qVec SourceL (qVec SourceL W)) (translate (binaryParameters Q 1) a) := by
        simpa using ih 0 (by simp) s s' ((n+1)+1) ((n'+1)+1) (binaryParameters P 1)
          (binaryParameters Q 1) w (qVec SourceL (qVec SourceL W)) (by simpa using ha) hw
          hW.qVec.qVec hp1 hq1 (hrel.1.binaryOne hP hQ hW) (by simpa using hl1)
          (by simpa using hl1')
      have hright : translate (binaryParameters P 0) (termSubst PA194PAeq.language w b) =
          subst SourceL (qVec SourceL (qVec SourceL W)) (translate (binaryParameters Q 0) b) := by
        simpa using ih 1 (by simp) s s' ((n+1)+1) ((n'+1)+1) (binaryParameters P 0)
          (binaryParameters Q 0) w (qVec SourceL (qVec SourceL W)) (by simpa using hb) hw
          hW.qVec.qVec hp0 hq0 (hrel.1.binaryZero hP hQ hW) (by simpa using hl0)
          (by simpa using hl0')
      have hsl := scope_translate ha.isUTerm s' ((n'+1)+1) (binaryParameters Q 1) ha hq1 hl1
      have hsr := scope_translate hb.isUTerm s' ((n'+1)+1) (binaryParameters Q 0) hb hq0 hl0
      rcases htwo with rfl | rfl
      · rw [translate_add P _ _ hsa.isUTerm hsb.isUTerm, translate_add Q a b ha.isUTerm hb.isUTerm,
          binaryValue_subst additionTemplate hQ.2.2 hsl hsr hW, hrel.2, hleft, hright]
      · rw [translate_mul P _ _ hsa.isUTerm hsb.isUTerm, translate_mul Q a b ha.isUTerm hb.isUTerm,
          binaryValue_subst multiplicationTemplate hQ.2.2 hsl hsr hW, hrel.2, hleft, hright]

/-! ### Formulas -/

theorem atomicEquality_subst {s s' n n' P Q w W a b : V} (hP : ParametersValid s n P)
    (hQ : ParametersValid s' n' Q) (hw : IsSemitermVec PA194PAeq.language s' s w)
    (hW : IsSemitermVec SourceL n' n W) (hrel : EnvSubstRel s s' P Q w W)
    (ha : IsSemiterm PA194PAeq.language s' a) (hb : IsSemiterm PA194PAeq.language s' b)
    (hla : a < len (nth Q 1)) (hlb : b < len (nth Q 1))
    (hla' : termSubst PA194PAeq.language w a < len (nth P 1))
    (hlb' : termSubst PA194PAeq.language w b < len (nth P 1)) :
    atomicEquality P (termSubst PA194PAeq.language w a) (termSubst PA194PAeq.language w b) =
      subst SourceL W (atomicEquality Q a b) := by
  have hp1 : ParametersValid s ((n+1)+1) (binaryParameters P 1) := binaryParameters_valid hP (by simp)
  have hp0 : ParametersValid s ((n+1)+1) (binaryParameters P 0) := binaryParameters_valid hP (by simp)
  have hq1 : ParametersValid s' ((n'+1)+1) (binaryParameters Q 1) := binaryParameters_valid hQ (by simp)
  have hq0 : ParametersValid s' ((n'+1)+1) (binaryParameters Q 0) := binaryParameters_valid hQ (by simp)
  have hfP := shiftTerms_valid hP.2.1
  have hfQ := shiftTerms_valid hQ.2.1
  have hl1 : a < len (nth (binaryParameters Q 1) 1) := by
    simpa [binaryParameters,shiftTerms_length hQ.2.1,shiftTerms_length hfQ] using hla
  have hl0 : b < len (nth (binaryParameters Q 0) 1) := by
    simpa [binaryParameters,shiftTerms_length hQ.2.1,shiftTerms_length hfQ] using hlb
  have hl1' : termSubst PA194PAeq.language w a < len (nth (binaryParameters P 1) 1) := by
    simpa [binaryParameters,shiftTerms_length hP.2.1,shiftTerms_length hfP] using hla'
  have hl0' : termSubst PA194PAeq.language w b < len (nth (binaryParameters P 0) 1) := by
    simpa [binaryParameters,shiftTerms_length hP.2.1,shiftTerms_length hfP] using hlb'
  have hleft := term_subst ha.isUTerm s s' ((n+1)+1) ((n'+1)+1) (binaryParameters P 1)
    (binaryParameters Q 1) w (qVec SourceL (qVec SourceL W)) ha hw hW.qVec.qVec hp1 hq1
    (hrel.binaryOne hP hQ hW) hl1 hl1'
  have hright := term_subst hb.isUTerm s s' ((n+1)+1) ((n'+1)+1) (binaryParameters P 0)
    (binaryParameters Q 0) w (qVec SourceL (qVec SourceL W)) hb hw hW.qVec.qVec hp0 hq0
    (hrel.binaryZero hP hQ hW) hl0 hl0'
  have hsl := scope_translate ha.isUTerm s' ((n'+1)+1) (binaryParameters Q 1) ha hq1 hl1
  have hsr := scope_translate hb.isUTerm s' ((n'+1)+1) (binaryParameters Q 0) hb hq0 hl0
  unfold atomicEquality
  rw [equalityOutput_subst hsl hsr hW, hleft, hright]

def FormulaSubstProperty (p : V) : Prop :=
  ∀ s s' n n' P Q w W, IsSemiformula PA194PAeq.language s' p →
    IsSemitermVec PA194PAeq.language s' s w → IsSemitermVec SourceL n' n W →
    ParametersValid s n P → ParametersValid s' n' Q → EnvSubstRel s s' P Q w W →
    p < len (nth Q 1) → subst PA194PAeq.language w p < len (nth P 1) →
    translateFormula P (subst PA194PAeq.language w p) = subst SourceL W (translateFormula Q p)
theorem FormulaSubstProperty_definable : 𝚷₁-Predicate (FormulaSubstProperty : V → Prop) := by
  haveI : 𝚺₁-Function₂ (translateFormula : V → V → V) := translateFormula_defined.to_definable
  unfold FormulaSubstProperty ParametersValid EnvSubstRel
  definability

theorem formula_subst {p : V} (hp : IsUFormula PA194PAeq.language p) : FormulaSubstProperty p := by
  apply IsUFormula.ISigma1.pi1_succ_induction FormulaSubstProperty_definable ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro k r v hr hv s s' n n' P Q w W hscope hw hW hP hQ hrel hlen hlen'
    have hsv := ((IsSemiformula.rel).mp hscope).2
    rw [substs_rel hr hv] at hlen' ⊢
    rcases (PA194PAeq.source_relations k r).mp hr with ⟨rfl,rfl⟩
    have ha : IsSemiterm PA194PAeq.language s' (nth v 0) := hsv.nth (by simp)
    have hb : IsSemiterm PA194PAeq.language s' (nth v 1) := hsv.nth (by simp)
    have hla : nth v 0 < len (nth Q 1) := lt_trans (nth_lt_qqRel_of_lt (by simp [←hv.lh])) hlen
    have hlb : nth v 1 < len (nth Q 1) := lt_trans (nth_lt_qqRel_of_lt (by simp [←hv.lh])) hlen
    have hv' : IsUTermVec PA194PAeq.language 2 (termSubstVec PA194PAeq.language 2 w v) :=
      (hw.termSubstVec hsv).isUTerm
    have h0 : nth (termSubstVec PA194PAeq.language 2 w v) 0 =
        termSubst PA194PAeq.language w (nth v 0) := nth_termSubstVec hv (by simp)
    have h1 : nth (termSubstVec PA194PAeq.language 2 w v) 1 =
        termSubst PA194PAeq.language w (nth v 1) := nth_termSubstVec hv (by simp)
    have hla' : termSubst PA194PAeq.language w (nth v 0) < len (nth P 1) := by
      rw [← h0]
      exact lt_trans (nth_lt_qqRel_of_lt (by rw [← hv'.lh]; simp)) hlen'
    have hlb' : termSubst PA194PAeq.language w (nth v 1) < len (nth P 1) := by
      rw [← h1]
      exact lt_trans (nth_lt_qqRel_of_lt (by rw [← hv'.lh]; simp)) hlen'
    rw [translate_rel P _ _ _ hr hv', translate_rel Q _ _ _ hr hv, h0, h1]
    exact atomicEquality_subst hP hQ hw hW hrel ha hb hla hlb hla' hlb'
  · intro k r v hr hv s s' n n' P Q w W hscope hw hW hP hQ hrel hlen hlen'
    have hsv := ((IsSemiformula.nrel).mp hscope).2
    rw [substs_nrel hr hv] at hlen' ⊢
    rcases (PA194PAeq.source_relations k r).mp hr with ⟨rfl,rfl⟩
    have ha : IsSemiterm PA194PAeq.language s' (nth v 0) := hsv.nth (by simp)
    have hb : IsSemiterm PA194PAeq.language s' (nth v 1) := hsv.nth (by simp)
    have hla : nth v 0 < len (nth Q 1) := lt_trans (nth_lt_qqNRel_of_lt (by simp [←hv.lh])) hlen
    have hlb : nth v 1 < len (nth Q 1) := lt_trans (nth_lt_qqNRel_of_lt (by simp [←hv.lh])) hlen
    have hv' : IsUTermVec PA194PAeq.language 2 (termSubstVec PA194PAeq.language 2 w v) :=
      (hw.termSubstVec hsv).isUTerm
    have h0 : nth (termSubstVec PA194PAeq.language 2 w v) 0 =
        termSubst PA194PAeq.language w (nth v 0) := nth_termSubstVec hv (by simp)
    have h1 : nth (termSubstVec PA194PAeq.language 2 w v) 1 =
        termSubst PA194PAeq.language w (nth v 1) := nth_termSubstVec hv (by simp)
    have hla' : termSubst PA194PAeq.language w (nth v 0) < len (nth P 1) := by
      rw [← h0]
      exact lt_trans (nth_lt_qqNRel_of_lt (by rw [← hv'.lh]; simp)) hlen'
    have hlb' : termSubst PA194PAeq.language w (nth v 1) < len (nth P 1) := by
      rw [← h1]
      exact lt_trans (nth_lt_qqNRel_of_lt (by rw [← hv'.lh]; simp)) hlen'
    rw [translate_nrel P _ _ _ hr hv', translate_nrel Q _ _ _ hr hv, h0, h1,
      substs_neg (atomicEquality_valid hQ ha hb hla hlb) hW,
      atomicEquality_subst hP hQ hw hW hrel ha hb hla hlb hla' hlb']
  · intro s s' n n' P Q w W _ _ _ _ _ _ _ _
    simp [translate_verum]
  · intro s s' n n' P Q w W _ _ _ _ _ _ _ _
    simp [translate_falsum]
  · intro a b ha hb iha ihb s s' n n' P Q w W hscope hw hW hP hQ hrel hlen hlen'
    have hsc := (IsSemiformula.and).mp hscope
    rw [substs_and ha hb] at hlen' ⊢
    have hla := lt_trans (lt_qqAnd_left a b) hlen
    have hlb := lt_trans (lt_qqAnd_right a b) hlen
    have hla' := lt_trans (lt_qqAnd_left _ _) hlen'
    have hlb' := lt_trans (lt_qqAnd_right _ _) hlen'
    have hta := formula_scope_translate ha s' n' Q hsc.1 hQ hla
    have htb := formula_scope_translate hb s' n' Q hsc.2 hQ hlb
    rw [translate_and P _ _ (hsc.1.subst hw).isUFormula (hsc.2.subst hw).isUFormula,
      translate_and Q a b ha hb, substs_and hta.isUFormula htb.isUFormula,
      iha s s' n n' P Q w W hsc.1 hw hW hP hQ hrel hla hla',
      ihb s s' n n' P Q w W hsc.2 hw hW hP hQ hrel hlb hlb']
  · intro a b ha hb iha ihb s s' n n' P Q w W hscope hw hW hP hQ hrel hlen hlen'
    have hsc := (IsSemiformula.or).mp hscope
    rw [substs_or ha hb] at hlen' ⊢
    have hla := lt_trans (lt_qqOr_left a b) hlen
    have hlb := lt_trans (lt_qqOr_right a b) hlen
    have hla' := lt_trans (lt_qqOr_left _ _) hlen'
    have hlb' := lt_trans (lt_qqOr_right _ _) hlen'
    have hta := formula_scope_translate ha s' n' Q hsc.1 hQ hla
    have htb := formula_scope_translate hb s' n' Q hsc.2 hQ hlb
    rw [translate_or P _ _ (hsc.1.subst hw).isUFormula (hsc.2.subst hw).isUFormula,
      translate_or Q a b ha hb, substs_or hta.isUFormula htb.isUFormula,
      iha s s' n n' P Q w W hsc.1 hw hW hP hQ hrel hla hla',
      ihb s s' n n' P Q w W hsc.2 hw hW hP hQ hrel hlb hlb']
  · intro a ha ih s s' n n' P Q w W hscope hw hW hP hQ hrel hlen hlen'
    have hsc : IsSemiformula PA194PAeq.language (s'+1) a := (IsSemiformula.all).mp hscope
    rw [substs_all ha] at hlen' ⊢
    have hchP : ParametersValid (s+1) (n+1) (formulaChildParameters P) := formulaChildParameters_valid hP
    have hchQ : ParametersValid (s'+1) (n'+1) (formulaChildParameters Q) := formulaChildParameters_valid hQ
    have hl : a < len (nth (formulaChildParameters Q) 1) := by
      simpa [formulaChildParameters,shiftTerms_length hQ.2.1] using lt_trans (lt_qqAll a) hlen
    have hl' : subst PA194PAeq.language (qVec PA194PAeq.language w) a <
        len (nth (formulaChildParameters P) 1) := by
      simpa [formulaChildParameters,shiftTerms_length hP.2.1] using lt_trans (lt_qqAll _) hlen'
    have hc := formula_scope_translate ha (s'+1) (n'+1) (formulaChildParameters Q) hsc hchQ hl
    rw [translate_all P _ (hsc.subst hw.qVec).isUFormula, translate_all Q a ha,
      allOutput_subst hc hW,
      ih (s+1) (s'+1) (n+1) (n'+1) (formulaChildParameters P) (formulaChildParameters Q)
        (qVec PA194PAeq.language w) (qVec SourceL W) hsc hw.qVec hW.qVec hchP hchQ
        (hrel.formulaChild hP hQ hw hW) hl hl']
  · intro a ha ih s s' n n' P Q w W hscope hw hW hP hQ hrel hlen hlen'
    have hsc : IsSemiformula PA194PAeq.language (s'+1) a := (IsSemiformula.exs).mp hscope
    rw [substs_ex ha] at hlen' ⊢
    have hchP : ParametersValid (s+1) (n+1) (formulaChildParameters P) := formulaChildParameters_valid hP
    have hchQ : ParametersValid (s'+1) (n'+1) (formulaChildParameters Q) := formulaChildParameters_valid hQ
    have hl : a < len (nth (formulaChildParameters Q) 1) := by
      simpa [formulaChildParameters,shiftTerms_length hQ.2.1] using lt_trans (lt_qqExs a) hlen
    have hl' : subst PA194PAeq.language (qVec PA194PAeq.language w) a <
        len (nth (formulaChildParameters P) 1) := by
      simpa [formulaChildParameters,shiftTerms_length hP.2.1] using lt_trans (lt_qqExs _) hlen'
    have hc := formula_scope_translate ha (s'+1) (n'+1) (formulaChildParameters Q) hsc hchQ hl
    rw [translate_exs P _ (hsc.subst hw.qVec).isUFormula, translate_exs Q a ha,
      exsOutput_subst hc hW,
      ih (s+1) (s'+1) (n+1) (n'+1) (formulaChildParameters P) (formulaChildParameters Q)
        (qVec PA194PAeq.language w) (qVec SourceL W) hsc hw.qVec hW.qVec hchP hchQ
        (hrel.formulaChild hP hQ hw hW) hl hl']

/-! ### The translation of `free p` -/

theorem IdentityPacket.child_free_nth {param i : V} (h : IdentityPacket param)
    (hi : i < len (nth param 1)) : nth (nth (formulaChildParameters param) 1) i = ^&i := by
  simp only [formulaChildParameters, parameters_free]
  rw [shiftTerms_nth h.1.2.1 hi, h.2 i hi, termBShift_fvar]
theorem IdentityPacket.child_free_len {param : V} (h : IdentityPacket param) :
    len (nth (formulaChildParameters param) 1) = len (nth param 1) := by
  simp only [formulaChildParameters, parameters_free]
  exact shiftTerms_length h.1.2.1

/-- The packet under one binder, with the bound variable instantiated by the free variable `j`. -/
theorem IdentityPacket.envSubstRel {param j : V} (h : IdentityPacket param)
    (hj : j < len (nth param 1)) :
    EnvSubstRel 0 1 param (formulaChildParameters param) (?[^&j] : V) (?[^&j] : V) := by
  refine ⟨?_,?_⟩
  · intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    refine Or.inr ⟨j,hj,by simp,?_⟩
    rw [h.2 j hj]
    simp [formulaChildParameters]
  · intro i hi
    rw [h.child_free_len] at hi
    refine ⟨hi,?_⟩
    rw [h.child_free_nth hi, h.2 i hi, termSubst_fvar]

/-- Under an identity packet, instantiating the bound variable of a formula of arity one by a
free variable commutes with the translation. -/
theorem translateFormula_substs1_fvar {param p j : V} (h : IdentityPacket param)
    (hp : IsSemiformula PA194PAeq.language 1 p) (hj : j < len (nth param 1))
    (hlen : p < len (nth param 1))
    (hslen : substs1 PA194PAeq.language (^&j) p < len (nth param 1)) :
    translateFormula param (substs1 PA194PAeq.language (^&j) p) =
      substs1 SourceL (^&j) (translateFormula (formulaChildParameters param) p) := by
  have hchild : ParametersValid 1 1 (formulaChildParameters param) := by
    simpa using formulaChildParameters_valid h.1
  have hw : IsSemitermVec PA194PAeq.language 1 0 (?[^&j] : V) := by simp
  have hW : IsSemitermVec SourceL 1 0 (?[^&j] : V) := by simp
  exact formula_subst hp.isUFormula 0 1 0 1 param (formulaChildParameters param)
    (?[^&j] : V) (?[^&j] : V) hp hw hW h.1 hchild (h.envSubstRel hj)
    (by rw [h.child_free_len]; exact hlen) hslen

/-- Under an identity packet, opening a bound variable commutes with the translation. -/
theorem translateFormula_free {param p : V} (h : IdentityPacket param)
    (hp : IsSemiformula PA194PAeq.language 1 p) (hlen : p < len (nth param 1))
    (hslen : shift PA194PAeq.language p < len (nth param 1))
    (hflen : free PA194PAeq.language p < len (nth param 1)) :
    translateFormula param (free PA194PAeq.language p) =
      free SourceL (translateFormula (formulaChildParameters param) p) := by
  have hchild : ParametersValid 1 1 (formulaChildParameters param) := by
    simpa using formulaChildParameters_valid h.1
  have hpos : 0 < len (nth param 1) := lt_of_le_of_lt (by simp) hlen
  have hrelS : EnvShiftRel 1 (formulaChildParameters param) (formulaChildParameters param) := by
    simpa using h.envShiftRel.formulaChild h.1 h.1
  have hA := formula_shift hp.isUFormula 1 1 (formulaChildParameters param)
    (formulaChildParameters param) hp hchild hchild hrelS (by rw [h.child_free_len]; exact hlen)
    (by rw [h.child_free_len]; exact hslen)
  have hB : translateFormula param (substs1 PA194PAeq.language (^&(0 : V))
        (shift PA194PAeq.language p)) =
      substs1 SourceL (^&(0 : V))
        (translateFormula (formulaChildParameters param) (shift PA194PAeq.language p)) :=
    translateFormula_substs1_fvar h hp.shift hpos hslen hflen
  show translateFormula param (substs1 PA194PAeq.language (^&(0 : V))
      (shift PA194PAeq.language p)) =
    substs1 SourceL (^&(0 : V)) (shift SourceL (translateFormula (formulaChildParameters param) p))
  rw [hB, hA]

/-! ### The universal rule -/

variable (U : Theory PA194PAeq.language) [U.Δ₁] (T : Theory SourceL) [T.Δ₁]

/-- The universal rule of the guarded compiler, for an identity packet. -/
theorem allRule_guarded {param : V} (hid : IdentityPacket param) (s p d : V)
    (hs : IsFormulaSet PA194PAeq.language s) (hmem : ^∀ p ∈ s)
    (hd : DerivationOf U d (insert (free PA194PAeq.language p) (setShift PA194PAeq.language s)))
    (hsize : allIntro s p d < len (nth param 1))
    (h : Guarded T param d (fstIdx d)) : Guarded T param (allIntro s p d) s := by
  have hlen : ∀ q ∈ s, q < len (nth param 1) :=
    seqMembers_bounded (lt_trans (seq_lt_allIntro s p d) hsize)
  have hdlen : d < len (nth param 1) := lt_trans (s_lt_allIntro s p d) hsize
  have hlen0 : ∀ q ∈ fstIdx d, q < len (nth param 1) := fun q hq =>
    lt_trans (lt_of_lt_of_le (lt_of_mem hq) (fstIdx_le_self d)) hdlen
  have hvalid := translatedSequent_valid hid.1 hs hlen
  have hall : IsSemiformula PA194PAeq.language 0 (^∀ p) := hs _ hmem
  have hp : IsSemiformula PA194PAeq.language 1 p := by simpa using (IsSemiformula.all).mp hall
  have hplen : p < len (nth param 1) := lt_trans (lt_qqAll p) (hlen _ hmem)
  have hfmem : free PA194PAeq.language p ∈ fstIdx d := by rw [hd.1]; simp
  have hsmem : ^∀ (shift PA194PAeq.language p) ∈ fstIdx d := by
    rw [hd.1, ← shift_all hp.isUFormula]
    exact mem_bitInsert_iff.mpr (Or.inr (shift_mem_setShift hmem))
  have hslen : shift PA194PAeq.language p < len (nth param 1) :=
    lt_trans (lt_qqAll _) (hlen0 _ hsmem)
  have hflen : free PA194PAeq.language p < len (nth param 1) := hlen0 _ hfmem
  have hchild : ParametersValid 1 1 (formulaChildParameters param) := by
    simpa using formulaChildParameters_valid hid.1
  have hC : IsSemiformula SourceL 1 (translateFormula (formulaChildParameters param) p) :=
    formula_scope_translate hp.isUFormula 1 1 (formulaChildParameters param) hp hchild
      (by rw [hid.child_free_len]; exact hplen)
  have hfree := translateFormula_free hid hp hplen hslen hflen
  have hbody : IsSemiformula SourceL 1
      (guardBody ^⋎ translateFormula (formulaChildParameters param) p) :=
    IsSemiformula.or.mpr ⟨guardBody_valid,hC⟩
  have hfreebody : free SourceL (guardBody ^⋎ translateFormula (formulaChildParameters param) p) =
      guard 0 ^⋎ free SourceL (translateFormula (formulaChildParameters param) p) := by
    have hw : IsSemitermVec SourceL 1 0 (?[^&(0 : V)] : V) := by simp
    show subst SourceL (?[^&(0 : V)] : V) (shift SourceL
        (guardBody ^⋎ translateFormula (formulaChildParameters param) p)) =
      guard 0 ^⋎ subst SourceL (?[^&(0 : V)] : V)
        (shift SourceL (translateFormula (formulaChildParameters param) p))
    rw [shift_or guardBody_valid.isUFormula hC.isUFormula,
      substs_or guardBody_valid.shift.isUFormula hC.shift.isUFormula]
    congr 1
    exact free_guardBody
  have htall : translateFormula param (^∀ p) =
      ^∀ (guardBody ^⋎ translateFormula (formulaChildParameters param) p) :=
    translate_all param p hp.isUFormula
  have h0 : Derivable T (guards d ∪ translatedSequent param (fstIdx d)) := h
  show Derivable T (guards (allIntro s p d) ∪ translatedSequent param s)
  have hΓ : IsFormulaSet SourceL (guards (allIntro s p d) ∪ translatedSequent param s) :=
    IsFormulaSet.union.mpr ⟨guards_valid _,hvalid⟩
  refine Derivable.all_m (p := guardBody ^⋎ translateFormula (formulaChildParameters param) p) ?_ ?_
  · rw [← htall]
    exact mem_cup_iff.mpr (Or.inr (translatedSequent_mem.mpr ⟨_,hmem,rfl⟩))
  · rw [hfreebody]
    have hfC : IsFormula SourceL (free SourceL (translateFormula (formulaChildParameters param) p)) :=
      hC.free
    refine Derivable.or_m (p := guard 0)
      (q := free SourceL (translateFormula (formulaChildParameters param) p))
      (mem_bitInsert_iff.mpr (Or.inl rfl)) ?_
    refine Derivable.wk (IsFormulaSet.insert_iff.mpr ⟨guard_valid 0,IsFormulaSet.insert_iff.mpr
      ⟨hfC,IsFormulaSet.insert_iff.mpr ⟨IsSemiformula.or.mpr ⟨guard_valid 0,hfC⟩,hΓ.setShift⟩⟩⟩) ?_ h0
    intro x hx
    rw [hd.1, translatedSequent_insert] at hx
    rcases mem_cup_iff.mp hx with hx | hx
    · have hx' := guards_succ_subset (allIntro s p d)
        (guards_mono (le_trans (le_of_lt (s_lt_allIntro s p d)) (by simp)) hx)
      rcases mem_bitInsert_iff.mp hx' with hx' | hx'
      · exact mem_bitInsert_iff.mpr (Or.inl hx')
      · refine mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr
          (mem_bitInsert_iff.mpr (Or.inr ?_)))))
        rw [mem_setShift_union]
        exact mem_cup_iff.mpr (Or.inl hx')
    · rcases mem_bitInsert_iff.mp hx with hx | hx
      · refine mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inl ?_)))
        rw [hx, hfree]
      · obtain ⟨q,hq,rfl⟩ := translatedSequent_mem.mp hx
        obtain ⟨q0,hq0,rfl⟩ := mem_setShift_iff.mp hq
        refine mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr
          (mem_bitInsert_iff.mpr (Or.inr ?_)))))
        rw [mem_setShift_union]
        refine mem_cup_iff.mpr (Or.inr (mem_setShift_iff.mpr
          ⟨translateFormula param q0,translatedSequent_mem.mpr ⟨q0,hq0,rfl⟩,?_⟩))
        exact translateFormula_shift hid (hs q0 hq0) (hlen q0 hq0)
          (hlen0 _ (by rw [hd.1]; exact mem_bitInsert_iff.mpr (Or.inr (shift_mem_setShift hq0))))

#print axioms term_subst
#print axioms formula_subst
#print axioms translateFormula_free
#print axioms allRule_guarded
end generic
end PA194GuardedCompiler
