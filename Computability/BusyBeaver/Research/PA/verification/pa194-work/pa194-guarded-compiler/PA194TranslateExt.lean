import PA194TranslateSubst
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The translation does not depend on the length of the free environment

Two packets that agree on the entries a formula reads give the same translation. With the
identity packets of Foundation's `fvarVec` this gives a translation `tr` of formulas of the
arithmetic language that has no size condition, and `trBody` for a formula under one binder.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Packets that agree -/

def EnvAgree (s P Q : V) : Prop :=
  (∀ i < s, nth (nth P 0) i = nth (nth Q 0) i) ∧
  (∀ i < len (nth P 1), i < len (nth Q 1) → nth (nth P 1) i = nth (nth Q 1) i)
def Agree (s P Q : V) : Prop := EnvAgree s P Q ∧ nth P 2 = nth Q 2

theorem EnvAgree.step {s n P Q : V} (r : V) (hP : ParametersValid s n P)
    (hQ : ParametersValid s n Q) (h : EnvAgree s P Q) :
    Agree s (parameters (shiftTerms (nth P 0)) (shiftTerms (nth P 1)) r)
      (parameters (shiftTerms (nth Q 0)) (shiftTerms (nth Q 1)) r) := by
  simp only [Agree, EnvAgree, parameters_bound, parameters_free, parameters_result]
  refine ⟨⟨?_,?_⟩,trivial⟩
  · intro i hi
    rw [shiftTerms_nth hP.1 hi, shiftTerms_nth hQ.1 hi, h.1 i hi]
  · intro i hi hi'
    rw [shiftTerms_length hP.2.1] at hi
    rw [shiftTerms_length hQ.2.1] at hi'
    rw [shiftTerms_nth hP.2.1 hi, shiftTerms_nth hQ.2.1 hi', h.2 i hi hi']
theorem EnvAgree.child {s n P Q : V} (hP : ParametersValid s n P) (hQ : ParametersValid s n Q)
    (h : EnvAgree s P Q) : Agree s (childParameters P) (childParameters Q) :=
  h.step (^#(0 : V)) hP hQ
theorem EnvAgree.binary {s n P Q : V} (j : V) (hP : ParametersValid s n P)
    (hQ : ParametersValid s n Q) (h : EnvAgree s P Q) :
    Agree s (binaryParameters P j) (binaryParameters Q j) := by
  have h1 : Agree s (childParameters P) (childParameters Q) := h.child hP hQ
  have h2 := EnvAgree.step (^#j) (childParameters_valid hP) (childParameters_valid hQ) h1.1
  simpa [childParameters, binaryParameters] using h2
theorem EnvAgree.formulaChild {s n P Q : V} (hP : ParametersValid s n P)
    (hQ : ParametersValid s n Q) (h : EnvAgree s P Q) :
    EnvAgree (s+1) (formulaChildParameters P) (formulaChildParameters Q) := by
  simp only [EnvAgree, formulaChildParameters, parameters_bound, parameters_free]
  refine ⟨?_,?_⟩
  · intro i hi
    rcases zero_or_succ i with (rfl | ⟨j,rfl⟩)
    · simp
    · have hj : j < s := by simpa using hi
      rw [nth_adjoin_succ, nth_adjoin_succ, shiftTerms_nth hP.1 hj, shiftTerms_nth hQ.1 hj,
        h.1 j hj]
  · intro i hi hi'
    rw [shiftTerms_length hP.2.1] at hi
    rw [shiftTerms_length hQ.2.1] at hi'
    rw [shiftTerms_nth hP.2.1 hi, shiftTerms_nth hQ.2.1 hi', h.2 i hi hi']

/-! ### Terms -/

def TermExtProperty (t : V) : Prop :=
  ∀ s n P Q, IsSemiterm PA194PAeq.language s t → ParametersValid s n P → ParametersValid s n Q →
    Agree s P Q → t < len (nth P 1) → t < len (nth Q 1) → translate P t = translate Q t
theorem TermExtProperty_definable : 𝚷₁-Predicate (TermExtProperty : V → Prop) := by
  haveI : 𝚺₁-Function₂ (translate : V → V → V) := translate_defined.to_definable
  unfold TermExtProperty ParametersValid Agree EnvAgree
  definability

theorem term_ext {t : V} (ht : IsUTerm PA194PAeq.language t) : TermExtProperty t := by
  apply IsUTerm.induction 𝚷 TermExtProperty_definable ?_ ?_ ?_ t ht
  · intro i s n P Q hterm hP hQ hrel hlen hlen'
    have hi : i < s := by simpa using hterm
    rw [translate_bound, translate_bound, hrel.2, hrel.1.1 i hi]
  · intro i s n P Q hterm hP hQ hrel hlen hlen'
    have hi : i < len (nth P 1) := lt_trans (lt_qqFvar i) hlen
    have hi' : i < len (nth Q 1) := lt_trans (lt_qqFvar i) hlen'
    rw [translate_free, translate_free, hrel.2, hrel.1.2 i hi hi']
  · intro k f v hf hv ih s n P Q hterm hP hQ hrel hlen hlen'
    have hsv : IsSemitermVec PA194PAeq.language k s v := ((IsSemiterm.func).mp hterm).2
    rcases (PA194PAeq.source_functions k f).mp hf with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,htwo⟩
    · have hv0 : v = 0 := len_zero_iff_eq_nil.mp hv.lh.symm
      subst v
      rw [translate_zero, translate_zero, hrel.2]
    · obtain ⟨a,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      have ha : IsSemiterm PA194PAeq.language s a := by
        simpa using hsv.nth (show (0 : V) < 1 by simp)
      have hlt : a < ^func (1 : V) 1 (?[a] : V) := by
        simpa using (nth_lt_qqFunc_of_lt (k := (1 : V)) (f := (1 : V)) (v := (?[a] : V))
          (i := (0 : V)) (by simp))
      have hl1 : a < len (nth (childParameters P) 1) := by
        simpa [childParameters, shiftTerms_length hP.2.1] using lt_trans hlt hlen
      have hl2 : a < len (nth (childParameters Q) 1) := by
        simpa [childParameters, shiftTerms_length hQ.2.1] using lt_trans hlt hlen'
      have hchild : translate (childParameters P) a = translate (childParameters Q) a := by
        simpa using ih 0 (by simp) s (n+1) (childParameters P) (childParameters Q)
          (by simpa using ha) (childParameters_valid hP) (childParameters_valid hQ)
          (hrel.1.child hP hQ) (by simpa using hl1) (by simpa using hl2)
      rw [translate_succ P a ha.isUTerm, translate_succ Q a ha.isUTerm, hrel.2, hchild]
    · obtain ⟨a,b,rfl⟩ := eq_doubleton_of_len_eq_two.mp hv.lh.symm
      have ha : IsSemiterm PA194PAeq.language s a := by
        simpa using hsv.nth (show (0 : V) < 2 by simp)
      have hb : IsSemiterm PA194PAeq.language s b := by
        simpa using hsv.nth (show (1 : V) < 2 by simp)
      have hlta : a < ^func (2 : V) f (?[a,b] : V) := by
        simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := f) (v := (?[a,b] : V))
          (i := (0 : V)) (by simp))
      have hltb : b < ^func (2 : V) f (?[a,b] : V) := by
        simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := f) (v := (?[a,b] : V))
          (i := (1 : V)) (by simp))
      have hfP := shiftTerms_valid hP.2.1
      have hfQ := shiftTerms_valid hQ.2.1
      have hl1 : a < len (nth (binaryParameters P 1) 1) := by
        simpa [binaryParameters,shiftTerms_length hP.2.1,shiftTerms_length hfP] using lt_trans hlta hlen
      have hl0 : b < len (nth (binaryParameters P 0) 1) := by
        simpa [binaryParameters,shiftTerms_length hP.2.1,shiftTerms_length hfP] using lt_trans hltb hlen
      have hl1' : a < len (nth (binaryParameters Q 1) 1) := by
        simpa [binaryParameters,shiftTerms_length hQ.2.1,shiftTerms_length hfQ] using lt_trans hlta hlen'
      have hl0' : b < len (nth (binaryParameters Q 0) 1) := by
        simpa [binaryParameters,shiftTerms_length hQ.2.1,shiftTerms_length hfQ] using lt_trans hltb hlen'
      have hleft : translate (binaryParameters P 1) a = translate (binaryParameters Q 1) a := by
        simpa using ih 0 (by simp) s ((n+1)+1) (binaryParameters P 1) (binaryParameters Q 1)
          (by simpa using ha) (binaryParameters_valid hP (by simp)) (binaryParameters_valid hQ (by simp))
          (hrel.1.binary 1 hP hQ) (by simpa using hl1) (by simpa using hl1')
      have hright : translate (binaryParameters P 0) b = translate (binaryParameters Q 0) b := by
        simpa using ih 1 (by simp) s ((n+1)+1) (binaryParameters P 0) (binaryParameters Q 0)
          (by simpa using hb) (binaryParameters_valid hP (by simp)) (binaryParameters_valid hQ (by simp))
          (hrel.1.binary 0 hP hQ) (by simpa using hl0) (by simpa using hl0')
      rcases htwo with rfl | rfl
      · rw [translate_add P a b ha.isUTerm hb.isUTerm, translate_add Q a b ha.isUTerm hb.isUTerm,
          hrel.2, hleft, hright]
      · rw [translate_mul P a b ha.isUTerm hb.isUTerm, translate_mul Q a b ha.isUTerm hb.isUTerm,
          hrel.2, hleft, hright]

/-! ### Formulas -/

theorem atomicEquality_ext {s n P Q a b : V} (hP : ParametersValid s n P)
    (hQ : ParametersValid s n Q) (hrel : EnvAgree s P Q)
    (ha : IsSemiterm PA194PAeq.language s a) (hb : IsSemiterm PA194PAeq.language s b)
    (hla : a < len (nth P 1)) (hlb : b < len (nth P 1))
    (hla' : a < len (nth Q 1)) (hlb' : b < len (nth Q 1)) :
    atomicEquality P a b = atomicEquality Q a b := by
  have hfP := shiftTerms_valid hP.2.1
  have hfQ := shiftTerms_valid hQ.2.1
  have hl1 : a < len (nth (binaryParameters P 1) 1) := by
    simpa [binaryParameters,shiftTerms_length hP.2.1,shiftTerms_length hfP] using hla
  have hl0 : b < len (nth (binaryParameters P 0) 1) := by
    simpa [binaryParameters,shiftTerms_length hP.2.1,shiftTerms_length hfP] using hlb
  have hl1' : a < len (nth (binaryParameters Q 1) 1) := by
    simpa [binaryParameters,shiftTerms_length hQ.2.1,shiftTerms_length hfQ] using hla'
  have hl0' : b < len (nth (binaryParameters Q 0) 1) := by
    simpa [binaryParameters,shiftTerms_length hQ.2.1,shiftTerms_length hfQ] using hlb'
  have hleft := term_ext ha.isUTerm s ((n+1)+1) (binaryParameters P 1) (binaryParameters Q 1)
    ha (binaryParameters_valid hP (by simp)) (binaryParameters_valid hQ (by simp))
    (hrel.binary 1 hP hQ) hl1 hl1'
  have hright := term_ext hb.isUTerm s ((n+1)+1) (binaryParameters P 0) (binaryParameters Q 0)
    hb (binaryParameters_valid hP (by simp)) (binaryParameters_valid hQ (by simp))
    (hrel.binary 0 hP hQ) hl0 hl0'
  unfold atomicEquality
  rw [hleft, hright]

def FormulaExtProperty (p : V) : Prop :=
  ∀ s n P Q, IsSemiformula PA194PAeq.language s p → ParametersValid s n P → ParametersValid s n Q →
    EnvAgree s P Q → p < len (nth P 1) → p < len (nth Q 1) →
    translateFormula P p = translateFormula Q p
theorem FormulaExtProperty_definable : 𝚷₁-Predicate (FormulaExtProperty : V → Prop) := by
  haveI : 𝚺₁-Function₂ (translateFormula : V → V → V) := translateFormula_defined.to_definable
  unfold FormulaExtProperty ParametersValid EnvAgree
  definability

theorem formula_ext {p : V} (hp : IsUFormula PA194PAeq.language p) : FormulaExtProperty p := by
  apply IsUFormula.ISigma1.pi1_succ_induction FormulaExtProperty_definable ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro k r v hr hv s n P Q hscope hP hQ hrel hlen hlen'
    have hsv := ((IsSemiformula.rel).mp hscope).2
    rcases (PA194PAeq.source_relations k r).mp hr with ⟨rfl,rfl⟩
    have ha : IsSemiterm PA194PAeq.language s (nth v 0) := hsv.nth (by simp)
    have hb : IsSemiterm PA194PAeq.language s (nth v 1) := hsv.nth (by simp)
    have h0 : nth v 0 < ^rel (2 : V) 0 v := nth_lt_qqRel_of_lt (by simp [←hv.lh])
    have h1 : nth v 1 < ^rel (2 : V) 0 v := nth_lt_qqRel_of_lt (by simp [←hv.lh])
    rw [translate_rel P _ _ _ hr hv, translate_rel Q _ _ _ hr hv]
    exact atomicEquality_ext hP hQ hrel ha hb (lt_trans h0 hlen) (lt_trans h1 hlen)
      (lt_trans h0 hlen') (lt_trans h1 hlen')
  · intro k r v hr hv s n P Q hscope hP hQ hrel hlen hlen'
    have hsv := ((IsSemiformula.nrel).mp hscope).2
    rcases (PA194PAeq.source_relations k r).mp hr with ⟨rfl,rfl⟩
    have ha : IsSemiterm PA194PAeq.language s (nth v 0) := hsv.nth (by simp)
    have hb : IsSemiterm PA194PAeq.language s (nth v 1) := hsv.nth (by simp)
    have h0 : nth v 0 < ^nrel (2 : V) 0 v := nth_lt_qqNRel_of_lt (by simp [←hv.lh])
    have h1 : nth v 1 < ^nrel (2 : V) 0 v := nth_lt_qqNRel_of_lt (by simp [←hv.lh])
    rw [translate_nrel P _ _ _ hr hv, translate_nrel Q _ _ _ hr hv,
      atomicEquality_ext hP hQ hrel ha hb (lt_trans h0 hlen) (lt_trans h1 hlen)
        (lt_trans h0 hlen') (lt_trans h1 hlen')]
  · intro s n P Q _ _ _ _ _ _
    rw [translate_verum, translate_verum]
  · intro s n P Q _ _ _ _ _ _
    rw [translate_falsum, translate_falsum]
  · intro a b ha hb iha ihb s n P Q hscope hP hQ hrel hlen hlen'
    have hsc := (IsSemiformula.and).mp hscope
    rw [translate_and P a b ha hb, translate_and Q a b ha hb,
      iha s n P Q hsc.1 hP hQ hrel (lt_trans (lt_qqAnd_left a b) hlen)
        (lt_trans (lt_qqAnd_left a b) hlen'),
      ihb s n P Q hsc.2 hP hQ hrel (lt_trans (lt_qqAnd_right a b) hlen)
        (lt_trans (lt_qqAnd_right a b) hlen')]
  · intro a b ha hb iha ihb s n P Q hscope hP hQ hrel hlen hlen'
    have hsc := (IsSemiformula.or).mp hscope
    rw [translate_or P a b ha hb, translate_or Q a b ha hb,
      iha s n P Q hsc.1 hP hQ hrel (lt_trans (lt_qqOr_left a b) hlen)
        (lt_trans (lt_qqOr_left a b) hlen'),
      ihb s n P Q hsc.2 hP hQ hrel (lt_trans (lt_qqOr_right a b) hlen)
        (lt_trans (lt_qqOr_right a b) hlen')]
  · intro a ha ih s n P Q hscope hP hQ hrel hlen hlen'
    have hsc : IsSemiformula PA194PAeq.language (s+1) a := (IsSemiformula.all).mp hscope
    have hl : a < len (nth (formulaChildParameters P) 1) := by
      simpa [formulaChildParameters,shiftTerms_length hP.2.1] using lt_trans (lt_qqAll a) hlen
    have hl' : a < len (nth (formulaChildParameters Q) 1) := by
      simpa [formulaChildParameters,shiftTerms_length hQ.2.1] using lt_trans (lt_qqAll a) hlen'
    rw [translate_all P a ha, translate_all Q a ha,
      ih (s+1) (n+1) (formulaChildParameters P) (formulaChildParameters Q) hsc
        (formulaChildParameters_valid hP) (formulaChildParameters_valid hQ)
        (hrel.formulaChild hP hQ) hl hl']
  · intro a ha ih s n P Q hscope hP hQ hrel hlen hlen'
    have hsc : IsSemiformula PA194PAeq.language (s+1) a := (IsSemiformula.exs).mp hscope
    have hl : a < len (nth (formulaChildParameters P) 1) := by
      simpa [formulaChildParameters,shiftTerms_length hP.2.1] using lt_trans (lt_qqExs a) hlen
    have hl' : a < len (nth (formulaChildParameters Q) 1) := by
      simpa [formulaChildParameters,shiftTerms_length hQ.2.1] using lt_trans (lt_qqExs a) hlen'
    rw [translate_exs P a ha, translate_exs Q a ha,
      ih (s+1) (n+1) (formulaChildParameters P) (formulaChildParameters Q) hsc
        (formulaChildParameters_valid hP) (formulaChildParameters_valid hQ)
        (hrel.formulaChild hP hQ) hl hl']

/-! ### The canonical identity packets -/

/-- The identity packet of length `L`. -/
noncomputable def idParam (L : V) : V := parameters 0 (fvarVec L) (^&(0 : V))
instance idParam_definable : 𝚺₁-Function₁ (idParam : V → V) := by
  haveI : 𝚺₁-Function₃ (parameters : V → V → V → V) := parameters_defined.to_definable
  show 𝚺₁-Function₁ (fun L : V => parameters 0 (fvarVec L) (^&(0 : V)))
  definability
@[simp] theorem idParam_len (L : V) : len (nth (idParam L) 1) = L := by
  simp [idParam]
theorem idParam_identity (L : V) : IdentityPacket (idParam L) := by
  refine ⟨?_,?_⟩
  · unfold ParametersValid idParam
    simp only [parameters_bound,parameters_free,parameters_result]
    refine ⟨by simp,?_,by simp⟩
    refine IsSemitermVec.iff.mpr ⟨rfl,?_⟩
    intro i hi
    rw [nth_fvarVec _ i (by simpa using hi)]
    simp
  · intro i hi
    rw [idParam_len] at hi
    simp only [idParam, parameters_free]
    exact nth_fvarVec _ i hi

theorem IdentityPacket.envAgree {P Q : V} (hP : IdentityPacket P) (hQ : IdentityPacket Q) :
    EnvAgree 0 P Q := by
  refine ⟨fun i hi => by simp at hi,fun i hi hi' => ?_⟩
  rw [hP.2 i hi, hQ.2 i hi']

/-- The translation of a formula of arity zero under a long enough identity packet. -/
noncomputable def tr (φ : V) : V := translateFormula (idParam (φ+1)) φ
/-- The translation of a formula of arity one under one binder. -/
noncomputable def trBody (p : V) : V := translateFormula (formulaChildParameters (idParam (p+1))) p
instance tr_definable : 𝚺₁-Function₁ (tr : V → V) := by
  haveI : 𝚺₁-Function₂ (translateFormula : V → V → V) := translateFormula_defined.to_definable
  show 𝚺₁-Function₁ (fun φ : V => translateFormula (idParam (φ+1)) φ)
  definability
instance trBody_definable : 𝚺₁-Function₁ (trBody : V → V) := by
  haveI : 𝚺₁-Function₂ (translateFormula : V → V → V) := translateFormula_defined.to_definable
  haveI : 𝚺₁-Function₁ (formulaChildParameters : V → V) := formulaChildParameters_defined.to_definable
  show 𝚺₁-Function₁ (fun p : V => translateFormula (formulaChildParameters (idParam (p+1))) p)
  definability

theorem tr_eq {param φ : V} (hid : IdentityPacket param)
    (hφ : IsSemiformula PA194PAeq.language 0 φ) (hlen : φ < len (nth param 1)) :
    translateFormula param φ = tr φ :=
  formula_ext hφ.isUFormula 0 0 param (idParam (φ+1)) hφ hid.1 (idParam_identity _).1
    (hid.envAgree (idParam_identity _)) hlen (by simp)
theorem trBody_eq {param p : V} (hid : IdentityPacket param)
    (hp : IsSemiformula PA194PAeq.language 1 p) (hlen : p < len (nth param 1)) :
    translateFormula (formulaChildParameters param) p = trBody p := by
  have h1 : ParametersValid 1 1 (formulaChildParameters param) := by
    simpa using formulaChildParameters_valid hid.1
  have h2 : ParametersValid 1 1 (formulaChildParameters (idParam (p+1))) := by
    simpa using formulaChildParameters_valid (idParam_identity (p+1)).1
  have hrel : EnvAgree 1 (formulaChildParameters param) (formulaChildParameters (idParam (p+1))) := by
    simpa using (hid.envAgree (idParam_identity (p+1))).formulaChild hid.1 (idParam_identity (p+1)).1
  exact formula_ext hp.isUFormula 1 1 _ _ hp h1 h2 hrel
    (by rw [hid.child_free_len]; exact hlen)
    (by rw [(idParam_identity (p+1)).child_free_len]; simp)

theorem lt_succ_of_le' {a b : V} (h : a ≤ b) : a < b + 1 := lt_of_le_of_lt h (lt_add_one b)

theorem tr_valid {φ : V} (hφ : IsSemiformula PA194PAeq.language 0 φ) :
    IsFormula SourceL (tr φ) :=
  formula_scope_translate hφ.isUFormula 0 0 (idParam (φ+1)) hφ (idParam_identity _).1 (by simp)
theorem trBody_valid {p : V} (hp : IsSemiformula PA194PAeq.language 1 p) :
    IsSemiformula SourceL 1 (trBody p) := by
  have h2 : ParametersValid 1 1 (formulaChildParameters (idParam (p+1))) := by
    simpa using formulaChildParameters_valid (idParam_identity (p+1)).1
  exact formula_scope_translate hp.isUFormula 1 1 _ hp h2
    (by rw [(idParam_identity (p+1)).child_free_len]; simp)

/-! ### `tr` and the connectives -/

theorem tr_verum : tr (^⊤ : V) = ^⊤ := translate_verum _
theorem tr_falsum : tr (^⊥ : V) = ^⊥ := translate_falsum _
theorem tr_and {a b : V} (ha : IsSemiformula PA194PAeq.language 0 a)
    (hb : IsSemiformula PA194PAeq.language 0 b) : tr (a ^⋏ b) = tr a ^⋏ tr b := by
  have hid := idParam_identity ((a ^⋏ b) + 1 : V)
  have h := translate_and (idParam ((a ^⋏ b) + 1)) a b ha.isUFormula hb.isUFormula
  rw [tr_eq hid ha (by simpa using lt_trans (lt_qqAnd_left a b) (lt_add_one _)),
    tr_eq hid hb (by simpa using lt_trans (lt_qqAnd_right a b) (lt_add_one _))] at h
  exact h
theorem tr_or {a b : V} (ha : IsSemiformula PA194PAeq.language 0 a)
    (hb : IsSemiformula PA194PAeq.language 0 b) : tr (a ^⋎ b) = tr a ^⋎ tr b := by
  have hid := idParam_identity ((a ^⋎ b) + 1 : V)
  have h := translate_or (idParam ((a ^⋎ b) + 1)) a b ha.isUFormula hb.isUFormula
  rw [tr_eq hid ha (by simpa using lt_trans (lt_qqOr_left a b) (lt_add_one _)),
    tr_eq hid hb (by simpa using lt_trans (lt_qqOr_right a b) (lt_add_one _))] at h
  exact h
theorem tr_all {p : V} (hp : IsSemiformula PA194PAeq.language 1 p) :
    tr (^∀ p) = ^∀ (guardBody ^⋎ trBody p) := by
  have hid := idParam_identity ((^∀ p) + 1 : V)
  have h := translate_all (idParam ((^∀ p) + 1)) p hp.isUFormula
  rw [trBody_eq hid hp (by simpa using lt_trans (lt_qqAll p) (lt_add_one _))] at h
  exact h
theorem tr_exs {p : V} (hp : IsSemiformula PA194PAeq.language 1 p) :
    tr (^∃ p) = ^∃ (domainCode (^#(0 : V)) ^⋏ trBody p) := by
  have hid := idParam_identity ((^∃ p) + 1 : V)
  have h := translate_exs (idParam ((^∃ p) + 1)) p hp.isUFormula
  rw [trBody_eq hid hp (by simpa using lt_trans (lt_qqExs p) (lt_add_one _))] at h
  exact h
theorem tr_neg {φ : V} (hφ : IsSemiformula PA194PAeq.language 0 φ) :
    tr (neg PA194PAeq.language φ) = neg SourceL (tr φ) := by
  have hid := idParam_identity (φ + neg PA194PAeq.language φ + 1 : V)
  have h1 : φ < len (nth (idParam (φ + neg PA194PAeq.language φ + 1)) 1) := by
    simpa using lt_succ_of_le' (le_self_add (a := φ) (b := neg PA194PAeq.language φ))
  have h2 : neg PA194PAeq.language φ < len (nth (idParam (φ + neg PA194PAeq.language φ + 1)) 1) := by
    simpa using lt_succ_of_le' (le_add_self (a := neg PA194PAeq.language φ) (b := φ))
  have h := translateFormula_neg hφ.isUFormula 0 0 _ hφ hid.1 h1 h2
  rw [tr_eq hid hφ h1, tr_eq hid (IsSemiformula.neg_iff.mpr hφ) h2] at h
  exact h
theorem tr_shift {φ : V} (hφ : IsSemiformula PA194PAeq.language 0 φ) :
    tr (shift PA194PAeq.language φ) = shift SourceL (tr φ) := by
  have hid := idParam_identity (φ + shift PA194PAeq.language φ + 1 : V)
  have h1 : φ < len (nth (idParam (φ + shift PA194PAeq.language φ + 1)) 1) := by
    simpa using lt_succ_of_le' (le_self_add (a := φ) (b := shift PA194PAeq.language φ))
  have h2 : shift PA194PAeq.language φ <
      len (nth (idParam (φ + shift PA194PAeq.language φ + 1)) 1) := by
    simpa using lt_succ_of_le' (le_add_self (a := shift PA194PAeq.language φ) (b := φ))
  have h := translateFormula_shift hid hφ h1 h2
  rw [tr_eq hid hφ h1, tr_eq hid hφ.shift h2] at h
  exact h
theorem tr_substs1_fvar {p : V} (hp : IsSemiformula PA194PAeq.language 1 p) (j : V) :
    tr (substs1 PA194PAeq.language (^&j) p) = substs1 SourceL (^&j) (trBody p) := by
  have hid := idParam_identity (p + substs1 PA194PAeq.language (^&j) p + j + 1 : V)
  have hj : j < len (nth (idParam (p + substs1 PA194PAeq.language (^&j) p + j + 1)) 1) := by
    simpa using lt_succ_of_le' (le_add_self (a := j) (b := p + substs1 PA194PAeq.language (^&j) p))
  have h1 : p < len (nth (idParam (p + substs1 PA194PAeq.language (^&j) p + j + 1)) 1) := by
    simpa using lt_succ_of_le' (le_trans (le_self_add (a := p)
      (b := substs1 PA194PAeq.language (^&j) p)) le_self_add)
  have h2 : substs1 PA194PAeq.language (^&j) p <
      len (nth (idParam (p + substs1 PA194PAeq.language (^&j) p + j + 1)) 1) := by
    simpa using lt_succ_of_le' (le_trans (le_add_self (a := substs1 PA194PAeq.language (^&j) p)
      (b := p)) le_self_add)
  have hs : IsSemiformula PA194PAeq.language 0 (substs1 PA194PAeq.language (^&j) p) :=
    IsSemiformula.substs1 (by simp) hp
  have h := translateFormula_substs1_fvar hid hp hj h1 h2
  rw [tr_eq hid hs h2, trBody_eq hid hp h1] at h
  exact h
theorem tr_free {p : V} (hp : IsSemiformula PA194PAeq.language 1 p) :
    tr (free PA194PAeq.language p) = free SourceL (trBody p) := by
  have h := tr_substs1_fvar hp.shift (0 : V)
  have hs : trBody (shift PA194PAeq.language p) = shift SourceL (trBody p) := by
    have hid := idParam_identity (p + shift PA194PAeq.language p + 1 : V)
    have h1 : p < len (nth (idParam (p + shift PA194PAeq.language p + 1)) 1) := by
      simpa using lt_succ_of_le' (le_self_add (a := p) (b := shift PA194PAeq.language p))
    have h2 : shift PA194PAeq.language p <
        len (nth (idParam (p + shift PA194PAeq.language p + 1)) 1) := by
      simpa using lt_succ_of_le' (le_add_self (a := shift PA194PAeq.language p) (b := p))
    have hchild : ParametersValid 1 1 (formulaChildParameters (idParam (p + shift PA194PAeq.language p + 1))) := by
      simpa using formulaChildParameters_valid hid.1
    have hrelS : EnvShiftRel 1 (formulaChildParameters (idParam (p + shift PA194PAeq.language p + 1)))
        (formulaChildParameters (idParam (p + shift PA194PAeq.language p + 1))) := by
      simpa using hid.envShiftRel.formulaChild hid.1 hid.1
    have hA := formula_shift hp.isUFormula 1 1 _ _ hp hchild hchild hrelS
      (by rw [hid.child_free_len]; exact h1) (by rw [hid.child_free_len]; exact h2)
    rw [trBody_eq hid hp.shift h2, trBody_eq hid hp h1] at hA
    exact hA
  rw [hs] at h
  exact h

#print axioms term_ext
#print axioms formula_ext
#print axioms tr_eq
#print axioms trBody_eq
#print axioms tr_neg
#print axioms tr_shift
#print axioms tr_free
end generic
end PA194GuardedCompiler
