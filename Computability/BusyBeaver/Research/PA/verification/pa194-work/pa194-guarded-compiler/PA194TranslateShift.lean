import PA194GuardedCompile
import PA194OrderIsoRew
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The translation commutes with the shift of free variables

For a packet whose free environment sends the free variable `i` to the source free variable
`i`, the translation of a shifted arithmetic formula is the shift of its translation. The
statement is proved for every internally valid formula code, by structural induction over
terms and formulas with the packets as parameters.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher
open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal
open M6.PA.RelationalSource.ND (eq)
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Fixed templates -/

theorem quote_shift_fixed {n : Nat} (p : Semiproposition SourceL n) (h : Rewriting.shift p = p) :
    shift SourceL (⌜p⌝ : V) = ⌜p⌝ := by
  rw [← Semiformula.quote_shift, h]

theorem zeroTemplate_shift : Rewriting.shift zeroTemplate = zeroTemplate := by
  simpa [zeroTemplate, Rewriting.shift, app_eq_rewAux] using zero_rew Rew.shift (.bvar 0)
theorem successorTemplate_shift : Rewriting.shift successorTemplate = successorTemplate := by
  simpa [successorTemplate, Rewriting.shift, app_eq_rewAux] using
    successor_rew Rew.shift (.bvar 0) (.bvar 1)
theorem equalityTemplate_shift : Rewriting.shift equalityTemplate = equalityTemplate := by
  simp [equalityTemplate, eq, Rewriting.shift, app_eq_rewAux, Semiformula.rewAux]
theorem orderIsoTemplate_shift : Rewriting.shift orderIsoTemplate = orderIsoTemplate := by
  simpa [orderIsoTemplate, Rewriting.shift, app_eq_rewAux] using
    PairGraph.orderIso_rew Rew.shift (.bvar 0) (.bvar 1)
theorem additionTemplate_shift : Rewriting.shift additionTemplate = additionTemplate := by
  simpa [additionTemplate, Rewriting.shift, app_eq_rewAux] using
    PairGraph.addResult_rew Rew.shift (.bvar 0) (.bvar 1) (.bvar 2)
theorem multiplicationTemplate_shift :
    Rewriting.shift multiplicationTemplate = multiplicationTemplate := by
  simpa [multiplicationTemplate, Rewriting.shift, app_eq_rewAux] using
    PairGraph.mulResult_rew Rew.shift (.bvar 0) (.bvar 1) (.bvar 2)

theorem templateOne_shift (p : Semiproposition SourceL 1) (h : Rewriting.shift p = p) {n z : V}
    (hz : IsSemiterm SourceL n z) :
    shift SourceL (templateOne p z) = templateOne p (termShift SourceL z) := by
  have hq : IsSemiformula SourceL 1 (⌜p⌝ : V) := by
    simp
  have hw : IsSemitermVec SourceL 1 n (?[z] : V) := by simp [hz]
  show shift SourceL (subst SourceL (?[z] : V) ⌜p⌝) =
    subst SourceL (?[termShift SourceL z] : V) ⌜p⌝
  rw [shift_substs hq hw, quote_shift_fixed p h, termShiftVec_cons₁ hz.isUTerm]
theorem templateTwo_shift (p : Semiproposition SourceL 2) (h : Rewriting.shift p = p) {n x z : V}
    (hx : IsSemiterm SourceL n x) (hz : IsSemiterm SourceL n z) :
    shift SourceL (templateTwo p x z) =
      templateTwo p (termShift SourceL x) (termShift SourceL z) := by
  have hq : IsSemiformula SourceL 2 (⌜p⌝ : V) := by
    simpa using Semiformula.quote_isSemiformula (V := V) p
  have hw : IsSemitermVec SourceL 2 n (?[x,z] : V) := by simp [hx,hz]
  show shift SourceL (subst SourceL (?[x,z] : V) ⌜p⌝) =
    subst SourceL (?[termShift SourceL x,termShift SourceL z] : V) ⌜p⌝
  rw [shift_substs hq hw, quote_shift_fixed p h, termShiftVec_cons₂ hx.isUTerm hz.isUTerm]
theorem templateThree_shift (p : Semiproposition SourceL 3) (h : Rewriting.shift p = p)
    {n x y z : V} (hx : IsSemiterm SourceL n x) (hy : IsSemiterm SourceL n y)
    (hz : IsSemiterm SourceL n z) :
    shift SourceL (templateThree p x y z) =
      templateThree p (termShift SourceL x) (termShift SourceL y) (termShift SourceL z) := by
  have hq : IsSemiformula SourceL 3 (⌜p⌝ : V) := by
    simpa using Semiformula.quote_isSemiformula (V := V) p
  have hw : IsSemitermVec SourceL 3 n (?[x,y,z] : V) := by
    simp [hx,hy,hz,show (3:V)=2+1 from two_add_one_eq_three.symm]
  have hyz : IsUTermVec SourceL 2 (?[y,z] : V) := by simp [hy.isUTerm,hz.isUTerm]
  have h3 : termShiftVec SourceL 3 (?[x,y,z] : V) =
      ?[termShift SourceL x,termShift SourceL y,termShift SourceL z] := by
    rw [show (3:V)=2+1 from two_add_one_eq_three.symm, termShiftVec_cons hx.isUTerm hyz,
      termShiftVec_cons₂ hy.isUTerm hz.isUTerm]
  show shift SourceL (subst SourceL (?[x,y,z] : V) ⌜p⌝) =
    subst SourceL (?[termShift SourceL x,termShift SourceL y,termShift SourceL z] : V) ⌜p⌝
  rw [shift_substs hq hw, quote_shift_fixed p h, h3]

theorem zeroCode_shift {n z : V} (hz : IsSemiterm SourceL n z) :
    shift SourceL (zeroCode z) = zeroCode (termShift SourceL z) :=
  templateOne_shift zeroTemplate zeroTemplate_shift hz
theorem equalityCode_shift {n x z : V} (hx : IsSemiterm SourceL n x) (hz : IsSemiterm SourceL n z) :
    shift SourceL (equalityCode x z) = equalityCode (termShift SourceL x) (termShift SourceL z) :=
  templateTwo_shift equalityTemplate equalityTemplate_shift hx hz
theorem successorCode_shift {n x z : V} (hx : IsSemiterm SourceL n x) (hz : IsSemiterm SourceL n z) :
    shift SourceL (successorCode x z) = successorCode (termShift SourceL x) (termShift SourceL z) :=
  templateTwo_shift successorTemplate successorTemplate_shift hx hz
theorem orderIsoCode_shift {n x z : V} (hx : IsSemiterm SourceL n x) (hz : IsSemiterm SourceL n z) :
    shift SourceL (orderIsoCode x z) = orderIsoCode (termShift SourceL x) (termShift SourceL z) :=
  templateTwo_shift orderIsoTemplate orderIsoTemplate_shift hx hz

/-! ### Value constructors -/

theorem variableValue_shift {n z x : V} (hz : IsSemiterm SourceL n z) (hx : IsSemiterm SourceL n x) :
    shift SourceL (variableValue z x) =
      variableValue (termShift SourceL z) (termShift SourceL x) := by
  unfold variableValue
  rw [shift_and (domainCode_valid hz).isUFormula (equalityCode_valid hz hx).isUFormula,
    domainCode_shift hz, equalityCode_shift hz hx]
theorem zeroValue_shift {n z : V} (hz : IsSemiterm SourceL n z) :
    shift SourceL (zeroValue z) = zeroValue (termShift SourceL z) := by
  unfold zeroValue
  rw [shift_and (domainCode_valid hz).isUFormula (zeroCode_valid hz).isUFormula,
    domainCode_shift hz, zeroCode_shift hz]
theorem successorValue_shift {n z c : V} (hz : IsSemiterm SourceL n z)
    (hc : IsSemiformula SourceL (n+1) c) :
    shift SourceL (successorValue z c) = successorValue (termShift SourceL z) (shift SourceL c) := by
  have hb : IsSemiterm SourceL (n+1) (termBShift SourceL z) := IsSemiterm.termBShift hz
  have h0 : IsSemiterm SourceL (n+1) (^#(0 : V)) := by simp
  have hs : IsSemiformula SourceL (n+1) (successorCode (^#(0 : V)) (termBShift SourceL z)) :=
    successorCode_valid h0 hb
  have hcs := IsSemiformula.and.mpr ⟨hc,hs⟩
  have he : IsSemiformula SourceL n (^∃ (c ^⋏ successorCode (^#(0 : V)) (termBShift SourceL z))) :=
    IsSemiformula.exs.mpr hcs
  unfold successorValue
  rw [shift_and (domainCode_valid hz).isUFormula he.isUFormula, shift_exs hcs.isUFormula,
    shift_and hc.isUFormula hs.isUFormula, domainCode_shift hz, successorCode_shift h0 hb,
    termShift_bvar, ← termBShift_termShift hz]
theorem binaryValue_shift (p : Semiproposition SourceL 3) (h : Rewriting.shift p = p)
    {n z l r : V} (hz : IsSemiterm SourceL n z) (hl : IsSemiformula SourceL ((n+1)+1) l)
    (hr : IsSemiformula SourceL ((n+1)+1) r) :
    shift SourceL (binaryValue p z l r) =
      binaryValue p (termShift SourceL z) (shift SourceL l) (shift SourceL r) := by
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
  rw [shift_and (domainCode_valid hz).isUFormula he2.isUFormula, shift_exs he1.isUFormula,
    shift_exs hlrt.isUFormula, shift_and hl.isUFormula hrt.isUFormula,
    shift_and hr.isUFormula ht.isUFormula, domainCode_shift hz, templateThree_shift p h h1 h0 hb,
    termShift_bvar, termShift_bvar, ← termBShift_termShift hb1, ← termBShift_termShift hz]
theorem equalityOutput_shift {n l r : V} (hl : IsSemiformula SourceL ((n+1)+1) l)
    (hr : IsSemiformula SourceL ((n+1)+1) r) :
    shift SourceL (^∃ (^∃ (l ^⋏ (r ^⋏ orderIsoCode (^#(1 : V)) (^#(0 : V)))))) =
      ^∃ (^∃ (shift SourceL l ^⋏ (shift SourceL r ^⋏ orderIsoCode (^#(1 : V)) (^#(0 : V))))) := by
  have h1 : IsSemiterm SourceL ((n+1)+1) (^#(1 : V)) := by simp
  have h0 : IsSemiterm SourceL ((n+1)+1) (^#(0 : V)) := by simp
  have ho : IsSemiformula SourceL ((n+1)+1) (orderIsoCode (^#(1 : V)) (^#(0 : V))) :=
    templateTwo_valid orderIsoTemplate h1 h0
  have hro := IsSemiformula.and.mpr ⟨hr,ho⟩
  have hlro := IsSemiformula.and.mpr ⟨hl,hro⟩
  have he : IsSemiformula SourceL (n+1)
      (^∃ (l ^⋏ (r ^⋏ orderIsoCode (^#(1 : V)) (^#(0 : V))))) := IsSemiformula.exs.mpr hlro
  rw [shift_exs he.isUFormula, shift_exs hlro.isUFormula, shift_and hl.isUFormula hro.isUFormula,
    shift_and hr.isUFormula ho.isUFormula, orderIsoCode_shift h1 h0, termShift_bvar, termShift_bvar]
theorem allOutput_shift {n c : V} (hc : IsSemiformula SourceL (n+1) c) :
    shift SourceL (allOutput c) = allOutput (shift SourceL c) := by
  have h0 : IsSemiterm SourceL (n+1) (^#(0 : V)) := by simp
  have hd : IsSemiformula SourceL (n+1) (domainCode (^#(0 : V))) := domainCode_valid h0
  have hnd : IsSemiformula SourceL (n+1) (neg SourceL (domainCode (^#(0 : V)))) :=
    IsSemiformula.neg_iff.mpr hd
  have himp : IsSemiformula SourceL (n+1) (neg SourceL (domainCode (^#(0 : V))) ^⋎ c) :=
    IsSemiformula.or.mpr ⟨hnd,hc⟩
  show shift SourceL (^∀ (neg SourceL (domainCode (^#(0 : V))) ^⋎ c)) =
    ^∀ (neg SourceL (domainCode (^#(0 : V))) ^⋎ shift SourceL c)
  rw [shift_all himp.isUFormula, shift_or hnd.isUFormula hc.isUFormula, shift_neg hd,
    domainCode_shift h0, termShift_bvar]
theorem exsOutput_shift {n c : V} (hc : IsSemiformula SourceL (n+1) c) :
    shift SourceL (exsOutput c) = exsOutput (shift SourceL c) := by
  have h0 : IsSemiterm SourceL (n+1) (^#(0 : V)) := by simp
  have hd : IsSemiformula SourceL (n+1) (domainCode (^#(0 : V))) := domainCode_valid h0
  have hand := IsSemiformula.and.mpr ⟨hd,hc⟩
  unfold exsOutput
  rw [shift_exs hand.isUFormula, shift_and hd.isUFormula hc.isUFormula, domainCode_shift h0,
    termShift_bvar]

/-! ### Packets related by a shift -/

/-- The environments of `Q` are those of `P` shifted, with the free one re-indexed by one. -/
def EnvShiftRel (s P Q : V) : Prop :=
  (∀ i < s, nth (nth Q 0) i = termShift SourceL (nth (nth P 0) i)) ∧
  (∀ i < len (nth P 1), i + 1 < len (nth Q 1) →
    nth (nth Q 1) (i+1) = termShift SourceL (nth (nth P 1) i))
/-- The same with the result term. -/
def ShiftRel (s P Q : V) : Prop :=
  EnvShiftRel s P Q ∧ nth Q 2 = termShift SourceL (nth P 2)

theorem EnvShiftRel.step {s n P Q r : V} (hP : ParametersValid s n P) (hQ : ParametersValid s n Q)
    (h : EnvShiftRel s P Q) (hr : termShift SourceL r = r) :
    ShiftRel s (parameters (shiftTerms (nth P 0)) (shiftTerms (nth P 1)) r)
      (parameters (shiftTerms (nth Q 0)) (shiftTerms (nth Q 1)) r) := by
  simp only [ShiftRel, EnvShiftRel, parameters_bound, parameters_free, parameters_result]
  refine ⟨⟨?_,?_⟩,hr.symm⟩
  · intro i hi
    rw [shiftTerms_nth hQ.1 hi, shiftTerms_nth hP.1 hi, h.1 i hi,
      termBShift_termShift (hP.1.nth hi)]
  · intro i hi hi'
    rw [shiftTerms_length hP.2.1] at hi
    rw [shiftTerms_length hQ.2.1] at hi'
    rw [shiftTerms_nth hQ.2.1 hi', shiftTerms_nth hP.2.1 hi, h.2 i hi hi',
      termBShift_termShift (hP.2.1.nth hi)]
theorem EnvShiftRel.child {s n P Q : V} (hP : ParametersValid s n P) (hQ : ParametersValid s n Q)
    (h : EnvShiftRel s P Q) : ShiftRel s (childParameters P) (childParameters Q) :=
  h.step hP hQ (r := ^#(0 : V)) (by simp)
theorem EnvShiftRel.binary {s n P Q : V} (j : V) (hP : ParametersValid s n P)
    (hQ : ParametersValid s n Q) (h : EnvShiftRel s P Q) :
    ShiftRel s (binaryParameters P j) (binaryParameters Q j) := by
  have h1 : ShiftRel s (childParameters P) (childParameters Q) := h.child hP hQ
  have h2 := EnvShiftRel.step (childParameters_valid hP) (childParameters_valid hQ) h1.1
    (r := ^#j) (by simp)
  simpa [childParameters, binaryParameters] using h2
theorem EnvShiftRel.formulaChild {s n P Q : V} (hP : ParametersValid s n P)
    (hQ : ParametersValid s n Q) (h : EnvShiftRel s P Q) :
    EnvShiftRel (s+1) (formulaChildParameters P) (formulaChildParameters Q) := by
  simp only [EnvShiftRel, formulaChildParameters, parameters_bound, parameters_free]
  refine ⟨?_,?_⟩
  · intro i hi
    rcases zero_or_succ i with (rfl | ⟨j,rfl⟩)
    · simp
    · have hj : j < s := by simpa using hi
      rw [nth_adjoin_succ, nth_adjoin_succ, shiftTerms_nth hQ.1 hj, shiftTerms_nth hP.1 hj,
        h.1 j hj, termBShift_termShift (hP.1.nth hj)]
  · intro i hi hi'
    rw [shiftTerms_length hP.2.1] at hi
    rw [shiftTerms_length hQ.2.1] at hi'
    rw [shiftTerms_nth hQ.2.1 hi', shiftTerms_nth hP.2.1 hi, h.2 i hi hi',
      termBShift_termShift (hP.2.1.nth hi)]

/-! ### Terms -/

def TermShiftProperty (t : V) : Prop :=
  ∀ s n P Q, IsSemiterm PA194PAeq.language s t → ParametersValid s n P → ParametersValid s n Q →
    ShiftRel s P Q → t < len (nth P 1) → termShift PA194PAeq.language t < len (nth Q 1) →
    translate Q (termShift PA194PAeq.language t) = shift SourceL (translate P t)
theorem TermShiftProperty_definable : 𝚷₁-Predicate (TermShiftProperty : V → Prop) := by
  haveI : 𝚺₁-Function₂ (translate : V → V → V) := translate_defined.to_definable
  unfold TermShiftProperty ParametersValid ShiftRel EnvShiftRel
  definability

theorem lt_qqFvar (j : V) : j < (^&j : V) := by
  change j < pair (1 : V) j + 1
  exact lt_of_le_of_lt (le_pair_right (1 : V) j) (lt_add_one _)

theorem term_shift {t : V} (ht : IsUTerm PA194PAeq.language t) : TermShiftProperty t := by
  apply IsUTerm.induction 𝚷 TermShiftProperty_definable ?_ ?_ ?_ t ht
  · intro i s n P Q hterm hP hQ hrel hlen hlen'
    have hi : i < s := by simpa using hterm
    rw [termShift_bvar, translate_bound, translate_bound,
      variableValue_shift hP.2.2 (hP.1.nth hi), ← hrel.2, ← hrel.1.1 i hi]
  · intro i s n P Q hterm hP hQ hrel hlen hlen'
    have hi : i < len (nth P 1) := lt_trans (lt_qqFvar i) hlen
    rw [termShift_fvar] at hlen'
    have hi' : i + 1 < len (nth Q 1) := lt_trans (lt_qqFvar (i+1)) hlen'
    rw [termShift_fvar, translate_free, translate_free,
      variableValue_shift hP.2.2 (hP.2.1.nth hi), ← hrel.2, ← hrel.1.2 i hi hi']
  · intro k f v hf hv ih s n P Q hterm hP hQ hrel hlen hlen'
    have hsv : IsSemitermVec PA194PAeq.language k s v := ((IsSemiterm.func).mp hterm).2
    rw [termShift_func hf hv] at hlen' ⊢
    rcases (PA194PAeq.source_functions k f).mp hf with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,htwo⟩
    · have hv0 : v = 0 := len_zero_iff_eq_nil.mp hv.lh.symm
      subst v
      rw [termShiftVec_nil, translate_zero, translate_zero, zeroValue_shift hP.2.2, hrel.2]
    · obtain ⟨a,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      have ha : IsSemiterm PA194PAeq.language s a := by
        simpa using hsv.nth (show (0 : V) < 1 by simp)
      rw [termShiftVec_cons₁ ha.isUTerm] at hlen' ⊢
      have hca : a < len (nth P 1) := lt_trans (by
        simpa using (nth_lt_qqFunc_of_lt (k := (1 : V)) (f := (1 : V)) (v := (?[a] : V))
          (i := (0 : V)) (by simp))) hlen
      have hca' : termShift PA194PAeq.language a < len (nth Q 1) := lt_trans (by
        simpa using (nth_lt_qqFunc_of_lt (k := (1 : V)) (f := (1 : V))
          (v := (?[termShift PA194PAeq.language a] : V)) (i := (0 : V)) (by simp))) hlen'
      have hcp : ParametersValid s (n+1) (childParameters P) := childParameters_valid hP
      have hcq : ParametersValid s (n+1) (childParameters Q) := childParameters_valid hQ
      have hl1 : a < len (nth (childParameters P) 1) := by
        simpa [childParameters, shiftTerms_length hP.2.1] using hca
      have hl2 : termShift PA194PAeq.language a < len (nth (childParameters Q) 1) := by
        simpa [childParameters, shiftTerms_length hQ.2.1] using hca'
      have hchild : translate (childParameters Q) (termShift PA194PAeq.language a) =
          shift SourceL (translate (childParameters P) a) := by
        simpa using ih 0 (by simp) s (n+1) (childParameters P) (childParameters Q)
          (by simpa using ha) hcp hcq (hrel.1.child hP hQ) (by simpa using hl1) (by simpa using hl2)
      have hscope := scope_translate ha.isUTerm s (n+1) (childParameters P) ha hcp hl1
      rw [translate_succ Q _ ha.isUTerm.termShift, translate_succ P a ha.isUTerm,
        successorValue_shift hP.2.2 hscope, hrel.2, hchild]
    · obtain ⟨a,b,rfl⟩ := eq_doubleton_of_len_eq_two.mp hv.lh.symm
      have ha : IsSemiterm PA194PAeq.language s a := by
        simpa using hsv.nth (show (0 : V) < 2 by simp)
      have hb : IsSemiterm PA194PAeq.language s b := by
        simpa using hsv.nth (show (1 : V) < 2 by simp)
      rw [termShiftVec_cons₂ ha.isUTerm hb.isUTerm] at hlen' ⊢
      have hca : a < len (nth P 1) := lt_trans (by
        simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := f) (v := (?[a,b] : V))
          (i := (0 : V)) (by simp))) hlen
      have hcb : b < len (nth P 1) := lt_trans (by
        simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := f) (v := (?[a,b] : V))
          (i := (1 : V)) (by simp))) hlen
      have hca' : termShift PA194PAeq.language a < len (nth Q 1) := lt_trans (by
        simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := f)
          (v := (?[termShift PA194PAeq.language a,termShift PA194PAeq.language b] : V))
          (i := (0 : V)) (by simp))) hlen'
      have hcb' : termShift PA194PAeq.language b < len (nth Q 1) := lt_trans (by
        simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := f)
          (v := (?[termShift PA194PAeq.language a,termShift PA194PAeq.language b] : V))
          (i := (1 : V)) (by simp))) hlen'
      have hp1 : ParametersValid s ((n+1)+1) (binaryParameters P 1) :=
        binaryParameters_valid hP (by simp)
      have hp0 : ParametersValid s ((n+1)+1) (binaryParameters P 0) :=
        binaryParameters_valid hP (by simp)
      have hq1 : ParametersValid s ((n+1)+1) (binaryParameters Q 1) :=
        binaryParameters_valid hQ (by simp)
      have hq0 : ParametersValid s ((n+1)+1) (binaryParameters Q 0) :=
        binaryParameters_valid hQ (by simp)
      have hfP := shiftTerms_valid hP.2.1
      have hfQ := shiftTerms_valid hQ.2.1
      have hl1 : a < len (nth (binaryParameters P 1) 1) := by
        simpa [binaryParameters,shiftTerms_length hP.2.1,shiftTerms_length hfP] using hca
      have hl0 : b < len (nth (binaryParameters P 0) 1) := by
        simpa [binaryParameters,shiftTerms_length hP.2.1,shiftTerms_length hfP] using hcb
      have hl1' : termShift PA194PAeq.language a < len (nth (binaryParameters Q 1) 1) := by
        simpa [binaryParameters,shiftTerms_length hQ.2.1,shiftTerms_length hfQ] using hca'
      have hl0' : termShift PA194PAeq.language b < len (nth (binaryParameters Q 0) 1) := by
        simpa [binaryParameters,shiftTerms_length hQ.2.1,shiftTerms_length hfQ] using hcb'
      have hleft : translate (binaryParameters Q 1) (termShift PA194PAeq.language a) =
          shift SourceL (translate (binaryParameters P 1) a) := by
        simpa using ih 0 (by simp) s ((n+1)+1) (binaryParameters P 1) (binaryParameters Q 1)
          (by simpa using ha) hp1 hq1 (hrel.1.binary 1 hP hQ) (by simpa using hl1)
          (by simpa using hl1')
      have hright : translate (binaryParameters Q 0) (termShift PA194PAeq.language b) =
          shift SourceL (translate (binaryParameters P 0) b) := by
        simpa using ih 1 (by simp) s ((n+1)+1) (binaryParameters P 0) (binaryParameters Q 0)
          (by simpa using hb) hp0 hq0 (hrel.1.binary 0 hP hQ) (by simpa using hl0)
          (by simpa using hl0')
      have hsl := scope_translate ha.isUTerm s ((n+1)+1) (binaryParameters P 1) ha hp1 hl1
      have hsr := scope_translate hb.isUTerm s ((n+1)+1) (binaryParameters P 0) hb hp0 hl0
      rcases htwo with rfl | rfl
      · rw [translate_add Q _ _ ha.isUTerm.termShift hb.isUTerm.termShift,
          translate_add P a b ha.isUTerm hb.isUTerm,
          binaryValue_shift additionTemplate additionTemplate_shift hP.2.2 hsl hsr,
          hrel.2, hleft, hright]
      · rw [translate_mul Q _ _ ha.isUTerm.termShift hb.isUTerm.termShift,
          translate_mul P a b ha.isUTerm hb.isUTerm,
          binaryValue_shift multiplicationTemplate multiplicationTemplate_shift hP.2.2 hsl hsr,
          hrel.2, hleft, hright]

/-! ### Formulas -/

theorem atomicEquality_shift {s n P Q a b : V} (hP : ParametersValid s n P)
    (hQ : ParametersValid s n Q) (hrel : EnvShiftRel s P Q)
    (ha : IsSemiterm PA194PAeq.language s a) (hb : IsSemiterm PA194PAeq.language s b)
    (hla : a < len (nth P 1)) (hlb : b < len (nth P 1))
    (hla' : termShift PA194PAeq.language a < len (nth Q 1))
    (hlb' : termShift PA194PAeq.language b < len (nth Q 1)) :
    atomicEquality Q (termShift PA194PAeq.language a) (termShift PA194PAeq.language b) =
      shift SourceL (atomicEquality P a b) := by
  have hp1 : ParametersValid s ((n+1)+1) (binaryParameters P 1) := binaryParameters_valid hP (by simp)
  have hp0 : ParametersValid s ((n+1)+1) (binaryParameters P 0) := binaryParameters_valid hP (by simp)
  have hq1 : ParametersValid s ((n+1)+1) (binaryParameters Q 1) := binaryParameters_valid hQ (by simp)
  have hq0 : ParametersValid s ((n+1)+1) (binaryParameters Q 0) := binaryParameters_valid hQ (by simp)
  have hfP := shiftTerms_valid hP.2.1
  have hfQ := shiftTerms_valid hQ.2.1
  have hl1 : a < len (nth (binaryParameters P 1) 1) := by
    simpa [binaryParameters,shiftTerms_length hP.2.1,shiftTerms_length hfP] using hla
  have hl0 : b < len (nth (binaryParameters P 0) 1) := by
    simpa [binaryParameters,shiftTerms_length hP.2.1,shiftTerms_length hfP] using hlb
  have hl1' : termShift PA194PAeq.language a < len (nth (binaryParameters Q 1) 1) := by
    simpa [binaryParameters,shiftTerms_length hQ.2.1,shiftTerms_length hfQ] using hla'
  have hl0' : termShift PA194PAeq.language b < len (nth (binaryParameters Q 0) 1) := by
    simpa [binaryParameters,shiftTerms_length hQ.2.1,shiftTerms_length hfQ] using hlb'
  have hleft := term_shift ha.isUTerm s ((n+1)+1) (binaryParameters P 1) (binaryParameters Q 1)
    ha hp1 hq1 (hrel.binary 1 hP hQ) hl1 hl1'
  have hright := term_shift hb.isUTerm s ((n+1)+1) (binaryParameters P 0) (binaryParameters Q 0)
    hb hp0 hq0 (hrel.binary 0 hP hQ) hl0 hl0'
  have hsl := scope_translate ha.isUTerm s ((n+1)+1) (binaryParameters P 1) ha hp1 hl1
  have hsr := scope_translate hb.isUTerm s ((n+1)+1) (binaryParameters P 0) hb hp0 hl0
  unfold atomicEquality
  rw [equalityOutput_shift hsl hsr, hleft, hright]

theorem lt_qqAnd_left (a b : V) : a < (a ^⋏ b) := by
  change a < pair (4 : V) (pair a b) + 1
  exact lt_of_le_of_lt (le_trans (le_pair_left a b) (le_pair_right (4 : V) (pair a b))) (lt_add_one _)
theorem lt_qqAnd_right (a b : V) : b < (a ^⋏ b) := by
  change b < pair (4 : V) (pair a b) + 1
  exact lt_of_le_of_lt (le_trans (le_pair_right a b) (le_pair_right (4 : V) (pair a b))) (lt_add_one _)
theorem lt_qqOr_left (a b : V) : a < (a ^⋎ b) := by
  change a < pair (5 : V) (pair a b) + 1
  exact lt_of_le_of_lt (le_trans (le_pair_left a b) (le_pair_right (5 : V) (pair a b))) (lt_add_one _)
theorem lt_qqOr_right (a b : V) : b < (a ^⋎ b) := by
  change b < pair (5 : V) (pair a b) + 1
  exact lt_of_le_of_lt (le_trans (le_pair_right a b) (le_pair_right (5 : V) (pair a b))) (lt_add_one _)
theorem lt_qqAll (a : V) : a < (^∀ a) := by
  change a < pair (6 : V) a + 1
  exact lt_of_le_of_lt (le_pair_right (6 : V) a) (lt_add_one _)
theorem lt_qqExs (a : V) : a < (^∃ a) := by
  change a < pair (7 : V) a + 1
  exact lt_of_le_of_lt (le_pair_right (7 : V) a) (lt_add_one _)

def FormulaShiftProperty (p : V) : Prop :=
  ∀ s n P Q, IsSemiformula PA194PAeq.language s p → ParametersValid s n P → ParametersValid s n Q →
    EnvShiftRel s P Q → p < len (nth P 1) → shift PA194PAeq.language p < len (nth Q 1) →
    translateFormula Q (shift PA194PAeq.language p) = shift SourceL (translateFormula P p)
theorem FormulaShiftProperty_definable : 𝚷₁-Predicate (FormulaShiftProperty : V → Prop) := by
  haveI : 𝚺₁-Function₂ (translateFormula : V → V → V) := translateFormula_defined.to_definable
  unfold FormulaShiftProperty ParametersValid EnvShiftRel
  definability

theorem formula_shift {p : V} (hp : IsUFormula PA194PAeq.language p) : FormulaShiftProperty p := by
  apply IsUFormula.ISigma1.pi1_succ_induction FormulaShiftProperty_definable ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro k r v hr hv s n P Q hscope hP hQ hrel hlen hlen'
    have hsv := ((IsSemiformula.rel).mp hscope).2
    rw [shift_rel hr hv] at hlen' ⊢
    rcases (PA194PAeq.source_relations k r).mp hr with ⟨rfl,rfl⟩
    have ha : IsSemiterm PA194PAeq.language s (nth v 0) := hsv.nth (by simp)
    have hb : IsSemiterm PA194PAeq.language s (nth v 1) := hsv.nth (by simp)
    have hla : nth v 0 < len (nth P 1) := lt_trans (nth_lt_qqRel_of_lt (by simp [←hv.lh])) hlen
    have hlb : nth v 1 < len (nth P 1) := lt_trans (nth_lt_qqRel_of_lt (by simp [←hv.lh])) hlen
    have hv' : IsUTermVec PA194PAeq.language 2 (termShiftVec PA194PAeq.language 2 v) := hv.termShiftVec
    have h0 : nth (termShiftVec PA194PAeq.language 2 v) 0 = termShift PA194PAeq.language (nth v 0) :=
      nth_termShiftVec hv (by simp)
    have h1 : nth (termShiftVec PA194PAeq.language 2 v) 1 = termShift PA194PAeq.language (nth v 1) :=
      nth_termShiftVec hv (by simp)
    have hla' : termShift PA194PAeq.language (nth v 0) < len (nth Q 1) := by
      rw [← h0]
      exact lt_trans (nth_lt_qqRel_of_lt (by simp [len_termShiftVec hv])) hlen'
    have hlb' : termShift PA194PAeq.language (nth v 1) < len (nth Q 1) := by
      rw [← h1]
      exact lt_trans (nth_lt_qqRel_of_lt (by simp [len_termShiftVec hv])) hlen'
    rw [translate_rel Q _ _ _ hr hv', translate_rel P _ _ _ hr hv, h0, h1]
    exact atomicEquality_shift hP hQ hrel ha hb hla hlb hla' hlb'
  · intro k r v hr hv s n P Q hscope hP hQ hrel hlen hlen'
    have hsv := ((IsSemiformula.nrel).mp hscope).2
    rw [shift_nrel hr hv] at hlen' ⊢
    rcases (PA194PAeq.source_relations k r).mp hr with ⟨rfl,rfl⟩
    have ha : IsSemiterm PA194PAeq.language s (nth v 0) := hsv.nth (by simp)
    have hb : IsSemiterm PA194PAeq.language s (nth v 1) := hsv.nth (by simp)
    have hla : nth v 0 < len (nth P 1) := lt_trans (nth_lt_qqNRel_of_lt (by simp [←hv.lh])) hlen
    have hlb : nth v 1 < len (nth P 1) := lt_trans (nth_lt_qqNRel_of_lt (by simp [←hv.lh])) hlen
    have hv' : IsUTermVec PA194PAeq.language 2 (termShiftVec PA194PAeq.language 2 v) := hv.termShiftVec
    have h0 : nth (termShiftVec PA194PAeq.language 2 v) 0 = termShift PA194PAeq.language (nth v 0) :=
      nth_termShiftVec hv (by simp)
    have h1 : nth (termShiftVec PA194PAeq.language 2 v) 1 = termShift PA194PAeq.language (nth v 1) :=
      nth_termShiftVec hv (by simp)
    have hla' : termShift PA194PAeq.language (nth v 0) < len (nth Q 1) := by
      rw [← h0]
      exact lt_trans (nth_lt_qqNRel_of_lt (by simp [len_termShiftVec hv])) hlen'
    have hlb' : termShift PA194PAeq.language (nth v 1) < len (nth Q 1) := by
      rw [← h1]
      exact lt_trans (nth_lt_qqNRel_of_lt (by simp [len_termShiftVec hv])) hlen'
    rw [translate_nrel Q _ _ _ hr hv', translate_nrel P _ _ _ hr hv, h0, h1,
      shift_neg (atomicEquality_valid hP ha hb hla hlb),
      atomicEquality_shift hP hQ hrel ha hb hla hlb hla' hlb']
  · intro s n P Q _ _ _ _ _ _
    simp [translate_verum]
  · intro s n P Q _ _ _ _ _ _
    simp [translate_falsum]
  · intro a b ha hb iha ihb s n P Q hscope hP hQ hrel hlen hlen'
    have hsc := (IsSemiformula.and).mp hscope
    rw [shift_and ha hb] at hlen' ⊢
    have hla := lt_trans (lt_qqAnd_left a b) hlen
    have hlb := lt_trans (lt_qqAnd_right a b) hlen
    have hla' := lt_trans (lt_qqAnd_left _ _) hlen'
    have hlb' := lt_trans (lt_qqAnd_right _ _) hlen'
    have hta := formula_scope_translate ha s n P hsc.1 hP hla
    have htb := formula_scope_translate hb s n P hsc.2 hP hlb
    rw [translate_and Q _ _ ha.shift hb.shift, translate_and P a b ha hb,
      shift_and hta.isUFormula htb.isUFormula,
      iha s n P Q hsc.1 hP hQ hrel hla hla', ihb s n P Q hsc.2 hP hQ hrel hlb hlb']
  · intro a b ha hb iha ihb s n P Q hscope hP hQ hrel hlen hlen'
    have hsc := (IsSemiformula.or).mp hscope
    rw [shift_or ha hb] at hlen' ⊢
    have hla := lt_trans (lt_qqOr_left a b) hlen
    have hlb := lt_trans (lt_qqOr_right a b) hlen
    have hla' := lt_trans (lt_qqOr_left _ _) hlen'
    have hlb' := lt_trans (lt_qqOr_right _ _) hlen'
    have hta := formula_scope_translate ha s n P hsc.1 hP hla
    have htb := formula_scope_translate hb s n P hsc.2 hP hlb
    rw [translate_or Q _ _ ha.shift hb.shift, translate_or P a b ha hb,
      shift_or hta.isUFormula htb.isUFormula,
      iha s n P Q hsc.1 hP hQ hrel hla hla', ihb s n P Q hsc.2 hP hQ hrel hlb hlb']
  · intro a ha ih s n P Q hscope hP hQ hrel hlen hlen'
    have hsc : IsSemiformula PA194PAeq.language (s+1) a := (IsSemiformula.all).mp hscope
    rw [shift_all ha] at hlen' ⊢
    have hchP : ParametersValid (s+1) (n+1) (formulaChildParameters P) := formulaChildParameters_valid hP
    have hchQ : ParametersValid (s+1) (n+1) (formulaChildParameters Q) := formulaChildParameters_valid hQ
    have hl : a < len (nth (formulaChildParameters P) 1) := by
      simpa [formulaChildParameters,shiftTerms_length hP.2.1] using lt_trans (lt_qqAll a) hlen
    have hl' : shift PA194PAeq.language a < len (nth (formulaChildParameters Q) 1) := by
      simpa [formulaChildParameters,shiftTerms_length hQ.2.1] using lt_trans (lt_qqAll _) hlen'
    have hc := formula_scope_translate ha (s+1) (n+1) (formulaChildParameters P) hsc hchP hl
    rw [translate_all Q _ ha.shift, translate_all P a ha, allOutput_shift hc,
      ih (s+1) (n+1) (formulaChildParameters P) (formulaChildParameters Q) hsc hchP hchQ
        (hrel.formulaChild hP hQ) hl hl']
  · intro a ha ih s n P Q hscope hP hQ hrel hlen hlen'
    have hsc : IsSemiformula PA194PAeq.language (s+1) a := (IsSemiformula.exs).mp hscope
    rw [shift_exs ha] at hlen' ⊢
    have hchP : ParametersValid (s+1) (n+1) (formulaChildParameters P) := formulaChildParameters_valid hP
    have hchQ : ParametersValid (s+1) (n+1) (formulaChildParameters Q) := formulaChildParameters_valid hQ
    have hl : a < len (nth (formulaChildParameters P) 1) := by
      simpa [formulaChildParameters,shiftTerms_length hP.2.1] using lt_trans (lt_qqExs a) hlen
    have hl' : shift PA194PAeq.language a < len (nth (formulaChildParameters Q) 1) := by
      simpa [formulaChildParameters,shiftTerms_length hQ.2.1] using lt_trans (lt_qqExs _) hlen'
    have hc := formula_scope_translate ha (s+1) (n+1) (formulaChildParameters P) hsc hchP hl
    rw [translate_exs Q _ ha.shift, translate_exs P a ha, exsOutput_shift hc,
      ih (s+1) (n+1) (formulaChildParameters P) (formulaChildParameters Q) hsc hchP hchQ
        (hrel.formulaChild hP hQ) hl hl']

/-! ### The identity packet -/

/-- A packet valid at arities zero whose free environment sends `i` to the free variable `i`. -/
def IdentityPacket (param : V) : Prop :=
  ParametersValid 0 0 param ∧ ∀ i < len (nth param 1), nth (nth param 1) i = ^&i

theorem identityPacket_exists (L : V) :
    ∃ param : V, IdentityPacket param ∧ len (nth param 1) = L := by
  obtain ⟨v,hlen,hv⟩ := sigmaOne_skolem_vec (R := fun i y : V => y = ^&i) (by definability)
    (l := L) (fun i _ => ⟨_,rfl⟩)
  refine ⟨parameters 0 v (^&(0 : V)),⟨?_,?_⟩,by simpa using hlen⟩
  · unfold ParametersValid
    simp only [parameters_bound,parameters_free,parameters_result]
    refine ⟨by simp,?_,by simp⟩
    refine IsSemitermVec.iff.mpr ⟨rfl,?_⟩
    intro i hi
    rw [hv i (by simpa [hlen] using hi)]
    simp
  · intro i hi
    simp only [parameters_free] at hi ⊢
    exact hv i (by simpa [hlen] using hi)

theorem IdentityPacket.envShiftRel {param : V} (h : IdentityPacket param) :
    EnvShiftRel 0 param param := by
  refine ⟨fun i hi => by simp at hi,fun i hi hi' => ?_⟩
  rw [h.2 (i+1) hi', h.2 i hi, termShift_fvar]

/-- Under an identity packet the translation commutes with the shift. -/
theorem translateFormula_shift {param p : V} (h : IdentityPacket param)
    (hp : IsSemiformula PA194PAeq.language 0 p) (hlen : p < len (nth param 1))
    (hlen' : shift PA194PAeq.language p < len (nth param 1)) :
    translateFormula param (shift PA194PAeq.language p) = shift SourceL (translateFormula param p) :=
  formula_shift hp.isUFormula 0 0 param param hp h.1 h.1 h.envShiftRel hlen hlen'

#print axioms term_shift
#print axioms formula_shift
#print axioms identityPacket_exists
#print axioms translateFormula_shift
end generic
end PA194GuardedCompiler
