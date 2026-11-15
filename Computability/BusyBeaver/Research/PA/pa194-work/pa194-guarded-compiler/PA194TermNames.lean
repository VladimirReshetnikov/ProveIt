import PA194Leibniz
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The term facts from one function layer at a time

`TermFacts` is derived from `NameFacts`, a list of guarded facts each of which speaks about
one function symbol with its arguments as arbitrary internal terms. The facts are phrased with
three formulas of the arithmetic language in which the naming variable is quantified:

* `nameAll s s'`: every `x` with `x = s` has `x = s'`;
* `uniq s`: any two `x, y` with `x = s` and `y = s` have `x = y`;
* `exName s`: some `x` has `x = s`.

With these the inductions over terms need no eigenvariable: every step is a cut.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Terms and the three formulas -/

noncomputable def zeroT : V := ^func (0 : V) 0 0
noncomputable def succT (s : V) : V := ^func (1 : V) 1 (?[s] : V)
noncomputable def addT (s s' : V) : V := ^func (2 : V) 2 (?[s,s'] : V)
noncomputable def mulT (s s' : V) : V := ^func (2 : V) 3 (?[s,s'] : V)

/-- Every name of `s` is a name of `s'`. -/
noncomputable def nameAll (s s' : V) : V :=
  ^∀ (neg PA194PAeq.language (peq (^#(0 : V)) (termBShift PA194PAeq.language s)) ^⋎
    peq (^#(0 : V)) (termBShift PA194PAeq.language s'))
/-- Any two names of `s` are equal. -/
noncomputable def uniq (s : V) : V :=
  ^∀ (^∀ (neg PA194PAeq.language (peq (^#(1 : V))
      (termBShift PA194PAeq.language (termBShift PA194PAeq.language s))) ^⋎
    (neg PA194PAeq.language (peq (^#(0 : V))
      (termBShift PA194PAeq.language (termBShift PA194PAeq.language s))) ^⋎
      peq (^#(1 : V)) (^#(0 : V)))))
/-- `s` has a name. -/
noncomputable def exName (s : V) : V := ^∃ (peq (^#(0 : V)) (termBShift PA194PAeq.language s))

instance nameAll_definable : 𝚺₁-Function₂ (nameAll : V → V → V) := by
  show 𝚺₁-Function₂ (fun s s' : V =>
    ^∀ (neg PA194PAeq.language (peq (^#(0 : V)) (termBShift PA194PAeq.language s)) ^⋎
      peq (^#(0 : V)) (termBShift PA194PAeq.language s')))
  definability
instance uniq_definable : 𝚺₁-Function₁ (uniq : V → V) := by
  show 𝚺₁-Function₁ (fun s : V =>
    ^∀ (^∀ (neg PA194PAeq.language (peq (^#(1 : V))
        (termBShift PA194PAeq.language (termBShift PA194PAeq.language s))) ^⋎
      (neg PA194PAeq.language (peq (^#(0 : V))
        (termBShift PA194PAeq.language (termBShift PA194PAeq.language s))) ^⋎
        peq (^#(1 : V)) (^#(0 : V))))))
  definability
instance exName_definable : 𝚺₁-Function₁ (exName : V → V) := by
  show 𝚺₁-Function₁ (fun s : V => ^∃ (peq (^#(0 : V)) (termBShift PA194PAeq.language s)))
  definability

theorem zeroT_valid {n : V} : IsSemiterm PA194PAeq.language n (zeroT : V) := by
  unfold zeroT
  simp
theorem succT_valid {n s : V} (hs : IsSemiterm PA194PAeq.language n s) :
    IsSemiterm PA194PAeq.language n (succT s) := by
  unfold succT
  simp [hs]
theorem addT_valid {n s s' : V} (hs : IsSemiterm PA194PAeq.language n s)
    (hs' : IsSemiterm PA194PAeq.language n s') : IsSemiterm PA194PAeq.language n (addT s s') := by
  unfold addT
  simp [hs,hs']
theorem mulT_valid {n s s' : V} (hs : IsSemiterm PA194PAeq.language n s)
    (hs' : IsSemiterm PA194PAeq.language n s') : IsSemiterm PA194PAeq.language n (mulT s s') := by
  unfold mulT
  simp [hs,hs']

theorem nameAll_valid {s s' : V} (hs : IsSemiterm PA194PAeq.language 0 s)
    (hs' : IsSemiterm PA194PAeq.language 0 s') : IsSemiformula PA194PAeq.language 0 (nameAll s s') := by
  have h0 : IsSemiterm PA194PAeq.language 1 (^#(0 : V)) := by simp
  have hb : IsSemiformula PA194PAeq.language 1
      (neg PA194PAeq.language (peq (^#(0 : V)) (termBShift PA194PAeq.language s)) ^⋎
        peq (^#(0 : V)) (termBShift PA194PAeq.language s')) :=
    IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr (peq_valid h0 (bShift_valid hs)),
      peq_valid h0 (bShift_valid hs')⟩
  unfold nameAll
  exact IsSemiformula.all.mpr (by simpa using hb)
theorem uniq_valid {s : V} (hs : IsSemiterm PA194PAeq.language 0 s) :
    IsSemiformula PA194PAeq.language 0 (uniq s) := by
  have h1 : IsSemiterm PA194PAeq.language 2 (^#(1 : V)) := by simp
  have h0 : IsSemiterm PA194PAeq.language 2 (^#(0 : V)) := by simp
  have hb : IsSemiterm PA194PAeq.language 2
      (termBShift PA194PAeq.language (termBShift PA194PAeq.language s)) := by
    simpa [one_add_one_eq_two] using IsSemiterm.termBShift (bShift_valid hs)
  have hbody : IsSemiformula PA194PAeq.language 2
      (neg PA194PAeq.language (peq (^#(1 : V))
        (termBShift PA194PAeq.language (termBShift PA194PAeq.language s))) ^⋎
      (neg PA194PAeq.language (peq (^#(0 : V))
        (termBShift PA194PAeq.language (termBShift PA194PAeq.language s))) ^⋎
        peq (^#(1 : V)) (^#(0 : V)))) :=
    IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr (peq_valid h1 hb),
      IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr (peq_valid h0 hb),peq_valid h1 h0⟩⟩
  have hin : IsSemiformula PA194PAeq.language 1 (^∀
      (neg PA194PAeq.language (peq (^#(1 : V))
        (termBShift PA194PAeq.language (termBShift PA194PAeq.language s))) ^⋎
      (neg PA194PAeq.language (peq (^#(0 : V))
        (termBShift PA194PAeq.language (termBShift PA194PAeq.language s))) ^⋎
        peq (^#(1 : V)) (^#(0 : V))))) :=
    IsSemiformula.all.mpr (by simpa [one_add_one_eq_two] using hbody)
  unfold uniq
  exact IsSemiformula.all.mpr (by simpa using hin)
theorem exName_valid {s : V} (hs : IsSemiterm PA194PAeq.language 0 s) :
    IsSemiformula PA194PAeq.language 0 (exName s) := by
  have h0 : IsSemiterm PA194PAeq.language 1 (^#(0 : V)) := by simp
  unfold exName
  exact IsSemiformula.exs.mpr (by simpa using peq_valid h0 (bShift_valid hs))

/-- Substitution of one term for the bound variable of a term of arity one. -/
noncomputable def sb (t a : V) : V := termSubst PA194PAeq.language (?[t] : V) a
theorem sb_valid {t a : V} (ht : IsSemiterm PA194PAeq.language 0 t)
    (ha : IsSemiterm PA194PAeq.language 1 a) : IsSemiterm PA194PAeq.language 0 (sb t a) := by
  have hw : IsSemitermVec PA194PAeq.language 1 0 (?[t] : V) := by simp [ht]
  exact hw.termSubst ha
theorem sb_bvar (t : V) : sb t (^#(0 : V)) = t := by simp [sb]
theorem sb_fvar (t x : V) : sb t (^&x) = ^&x := by simp [sb]
theorem sb_zero (t : V) : sb t (zeroT : V) = zeroT := by
  unfold sb zeroT
  rw [termSubst_func (by simp) (by simp), termSubstVec_nil]
theorem sb_succ {t a : V} (ha : IsSemiterm PA194PAeq.language 1 a) :
    sb t (succT a) = succT (sb t a) := by
  have hv : IsUTermVec PA194PAeq.language 1 (?[a] : V) := by simp [ha.isUTerm]
  unfold sb succT
  rw [termSubst_func (by simp) hv, termSubstVec_cons₁ ha.isUTerm]
theorem sb_add {t a b : V} (ha : IsSemiterm PA194PAeq.language 1 a)
    (hb : IsSemiterm PA194PAeq.language 1 b) : sb t (addT a b) = addT (sb t a) (sb t b) := by
  have hv : IsUTermVec PA194PAeq.language 2 (?[a,b] : V) := by simp [ha.isUTerm,hb.isUTerm]
  unfold sb addT
  rw [termSubst_func (by simp) hv, termSubstVec_cons₂ ha.isUTerm hb.isUTerm]
theorem sb_mul {t a b : V} (ha : IsSemiterm PA194PAeq.language 1 a)
    (hb : IsSemiterm PA194PAeq.language 1 b) : sb t (mulT a b) = mulT (sb t a) (sb t b) := by
  have hv : IsUTermVec PA194PAeq.language 2 (?[a,b] : V) := by simp [ha.isUTerm,hb.isUTerm]
  unfold sb mulT
  rw [termSubst_func (by simp) hv, termSubstVec_cons₂ ha.isUTerm hb.isUTerm]

variable (T : Theory SourceL) [T.Δ₁]

/-- Guarded facts about one function layer, with arbitrary internal terms as arguments. -/
structure NameFacts : Prop where
  nRefl : ∀ s : V, IsSemiterm PA194PAeq.language 0 s →
    GDerivable T (insert (tr (nameAll s s)) (∅ : V))
  /-- If names transfer from `s₁` to `s₁'` and from `s₂` to `s₂'`, so does equality. -/
  atomTransfer : ∀ s₁ s₁' s₂ s₂' : V, IsSemiterm PA194PAeq.language 0 s₁ →
    IsSemiterm PA194PAeq.language 0 s₁' → IsSemiterm PA194PAeq.language 0 s₂ →
    IsSemiterm PA194PAeq.language 0 s₂' →
    GDerivable T (insert (neg SourceL (tr (nameAll s₁ s₁')))
      (insert (neg SourceL (tr (nameAll s₂ s₂')))
        (insert (neg SourceL (tr (peq s₁ s₂))) (insert (tr (peq s₁' s₂')) (∅ : V)))))
  nameOfUniq : ∀ t c : V, IsSemiterm PA194PAeq.language 0 t →
    GDerivable T (insert (neg SourceL (tr (uniq t)))
      (insert (neg SourceL (tr (peq (^&c) t))) (insert (tr (nameAll t (^&c))) (∅ : V))))
  nameOfEq : ∀ t c : V, IsSemiterm PA194PAeq.language 0 t →
    GDerivable T (insert (neg SourceL (tr (peq (^&c) t)))
      (insert (tr (nameAll (^&c) t)) (∅ : V)))
  nSucc : ∀ s s' : V, IsSemiterm PA194PAeq.language 0 s → IsSemiterm PA194PAeq.language 0 s' →
    GDerivable T (insert (neg SourceL (tr (nameAll s s')))
      (insert (tr (nameAll (succT s) (succT s'))) (∅ : V)))
  nAdd : ∀ s₁ s₁' s₂ s₂' : V, IsSemiterm PA194PAeq.language 0 s₁ →
    IsSemiterm PA194PAeq.language 0 s₁' → IsSemiterm PA194PAeq.language 0 s₂ →
    IsSemiterm PA194PAeq.language 0 s₂' →
    GDerivable T (insert (neg SourceL (tr (nameAll s₁ s₁')))
      (insert (neg SourceL (tr (nameAll s₂ s₂')))
        (insert (tr (nameAll (addT s₁ s₂) (addT s₁' s₂'))) (∅ : V))))
  nMul : ∀ s₁ s₁' s₂ s₂' : V, IsSemiterm PA194PAeq.language 0 s₁ →
    IsSemiterm PA194PAeq.language 0 s₁' → IsSemiterm PA194PAeq.language 0 s₂ →
    IsSemiterm PA194PAeq.language 0 s₂' →
    GDerivable T (insert (neg SourceL (tr (nameAll s₁ s₁')))
      (insert (neg SourceL (tr (nameAll s₂ s₂')))
        (insert (tr (nameAll (mulT s₁ s₂) (mulT s₁' s₂'))) (∅ : V))))
  uVar : ∀ i : V, GDerivable T (insert (tr (uniq (^&i))) (∅ : V))
  uZero : GDerivable T (insert (tr (uniq (zeroT : V))) (∅ : V))
  uSucc : ∀ s : V, IsSemiterm PA194PAeq.language 0 s →
    GDerivable T (insert (neg SourceL (tr (uniq s))) (insert (tr (uniq (succT s))) (∅ : V)))
  uAdd : ∀ s s' : V, IsSemiterm PA194PAeq.language 0 s → IsSemiterm PA194PAeq.language 0 s' →
    GDerivable T (insert (neg SourceL (tr (uniq s))) (insert (neg SourceL (tr (uniq s')))
      (insert (tr (uniq (addT s s'))) (∅ : V))))
  uMul : ∀ s s' : V, IsSemiterm PA194PAeq.language 0 s → IsSemiterm PA194PAeq.language 0 s' →
    GDerivable T (insert (neg SourceL (tr (uniq s))) (insert (neg SourceL (tr (uniq s')))
      (insert (tr (uniq (mulT s s'))) (∅ : V))))
  eVar : ∀ i : V, GDerivable T (insert (tr (exName (^&i))) (∅ : V))
  eZero : GDerivable T (insert (tr (exName (zeroT : V))) (∅ : V))
  eSucc : ∀ s : V, IsSemiterm PA194PAeq.language 0 s →
    GDerivable T (insert (neg SourceL (tr (exName s))) (insert (tr (exName (succT s))) (∅ : V)))
  eAdd : ∀ s s' : V, IsSemiterm PA194PAeq.language 0 s → IsSemiterm PA194PAeq.language 0 s' →
    GDerivable T (insert (neg SourceL (tr (exName s))) (insert (neg SourceL (tr (exName s')))
      (insert (tr (exName (addT s s'))) (∅ : V))))
  eMul : ∀ s s' : V, IsSemiterm PA194PAeq.language 0 s → IsSemiterm PA194PAeq.language 0 s' →
    GDerivable T (insert (neg SourceL (tr (exName s))) (insert (neg SourceL (tr (exName s')))
      (insert (tr (exName (mulT s s'))) (∅ : V))))

variable {T}

/-- Cut with weakening of both premises into a common context. -/
theorem GDerivable.cut_wk {Δ Δ₁ Δ₂ φ : V} (hΔ : IsFormulaSet SourceL Δ) (hφ : IsFormula SourceL φ)
    (h₁ : GDerivable T Δ₁) (h₂ : GDerivable T Δ₂) (s₁ : Δ₁ ⊆ insert φ Δ)
    (s₂ : Δ₂ ⊆ insert (neg SourceL φ) Δ) : GDerivable T Δ :=
  GDerivable.cut φ (GDerivable.wk (fs_cons hφ hΔ) s₁ h₁)
    (GDerivable.wk (fs_cons (IsSemiformula.neg_iff.mpr hφ) hΔ) s₂ h₂)

/-- A term of arity zero is a free variable or a function term whose arguments have arity
zero; this is the case analysis used by the three inductions. -/
theorem term_induction {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (hvar : ∀ i : V, P (^&i)) (hzero : P (zeroT : V))
    (hsucc : ∀ s : V, IsSemiterm PA194PAeq.language 0 s → P s → P (succT s))
    (hadd : ∀ s s' : V, IsSemiterm PA194PAeq.language 0 s → IsSemiterm PA194PAeq.language 0 s' →
      P s → P s' → P (addT s s'))
    (hmul : ∀ s s' : V, IsSemiterm PA194PAeq.language 0 s → IsSemiterm PA194PAeq.language 0 s' →
      P s → P s' → P (mulT s s')) :
    ∀ t : V, IsSemiterm PA194PAeq.language 0 t → P t := by
  apply IsSemiterm.induction 𝚺 hP
  · intro z hz
    simp at hz
  · exact hvar
  · intro k f v hf hv ih
    rcases (PA194PAeq.source_functions k f).mp hf with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,htwo⟩
    · have hv0 : v = 0 := len_zero_iff_eq_nil.mp hv.isUTerm.lh.symm
      subst v
      exact hzero
    · obtain ⟨a,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.isUTerm.lh.symm
      have ha : IsSemiterm PA194PAeq.language 0 a := by
        simpa using hv.nth (show (0 : V) < 1 by simp)
      exact hsucc a ha (by simpa using ih 0 (by simp))
    · obtain ⟨a,b,rfl⟩ := eq_doubleton_of_len_eq_two.mp hv.isUTerm.lh.symm
      have ha : IsSemiterm PA194PAeq.language 0 a := by
        simpa using hv.nth (show (0 : V) < 2 by simp)
      have hb : IsSemiterm PA194PAeq.language 0 b := by
        simpa using hv.nth (show (1 : V) < 2 by simp)
      have iha : P a := by simpa using ih 0 (by simp)
      have ihb : P b := by simpa using ih 1 (by simp)
      rcases htwo with rfl | rfl
      · exact hadd a b ha hb iha ihb
      · exact hmul a b ha hb iha ihb

/-- Any two names of a term are equal. -/
theorem uniq_all (N : NameFacts (V := V) T) :
    ∀ t : V, IsSemiterm PA194PAeq.language 0 t → GDerivable T (insert (tr (uniq t)) (∅ : V)) := by
  have hP : 𝚺₁-Predicate (fun t : V => GDerivable T (insert (tr (uniq t)) (∅ : V))) := by
    unfold GDerivable
    definability
  apply term_induction hP
  · exact N.uVar
  · exact N.uZero
  · intro s hs ih
    exact GDerivable.cut_wk (fs_cons (tr_valid (uniq_valid (succT_valid hs))) fs_nil)
      (tr_valid (uniq_valid hs)) ih (N.uSucc s hs) (by set_tac) (by set_tac)
  · intro s s' hs hs' ih ih'
    have hU := tr_valid (uniq_valid (addT_valid hs hs'))
    refine GDerivable.cut_wk (fs_cons hU fs_nil) (tr_valid (uniq_valid hs)) ih ?_
      (by set_tac) (fun x hx => hx)
    exact GDerivable.cut_wk (fs_cons (IsSemiformula.neg_iff.mpr (tr_valid (uniq_valid hs)))
      (fs_cons hU fs_nil)) (tr_valid (uniq_valid hs')) ih' (N.uAdd s s' hs hs')
      (by set_tac) (by set_tac)
  · intro s s' hs hs' ih ih'
    have hU := tr_valid (uniq_valid (mulT_valid hs hs'))
    refine GDerivable.cut_wk (fs_cons hU fs_nil) (tr_valid (uniq_valid hs)) ih ?_
      (by set_tac) (fun x hx => hx)
    exact GDerivable.cut_wk (fs_cons (IsSemiformula.neg_iff.mpr (tr_valid (uniq_valid hs)))
      (fs_cons hU fs_nil)) (tr_valid (uniq_valid hs')) ih' (N.uMul s s' hs hs')
      (by set_tac) (by set_tac)

/-- Every term has a name. -/
theorem exName_all (N : NameFacts (V := V) T) :
    ∀ t : V, IsSemiterm PA194PAeq.language 0 t → GDerivable T (insert (tr (exName t)) (∅ : V)) := by
  have hP : 𝚺₁-Predicate (fun t : V => GDerivable T (insert (tr (exName t)) (∅ : V))) := by
    unfold GDerivable
    definability
  apply term_induction hP
  · exact N.eVar
  · exact N.eZero
  · intro s hs ih
    exact GDerivable.cut_wk (fs_cons (tr_valid (exName_valid (succT_valid hs))) fs_nil)
      (tr_valid (exName_valid hs)) ih (N.eSucc s hs) (by set_tac) (by set_tac)
  · intro s s' hs hs' ih ih'
    have hU := tr_valid (exName_valid (addT_valid hs hs'))
    refine GDerivable.cut_wk (fs_cons hU fs_nil) (tr_valid (exName_valid hs)) ih ?_
      (by set_tac) (fun x hx => hx)
    exact GDerivable.cut_wk (fs_cons (IsSemiformula.neg_iff.mpr (tr_valid (exName_valid hs)))
      (fs_cons hU fs_nil)) (tr_valid (exName_valid hs')) ih' (N.eAdd s s' hs hs')
      (by set_tac) (by set_tac)
  · intro s s' hs hs' ih ih'
    have hU := tr_valid (exName_valid (mulT_valid hs hs'))
    refine GDerivable.cut_wk (fs_cons hU fs_nil) (tr_valid (exName_valid hs)) ih ?_
      (by set_tac) (fun x hx => hx)
    exact GDerivable.cut_wk (fs_cons (IsSemiformula.neg_iff.mpr (tr_valid (exName_valid hs)))
      (fs_cons hU fs_nil)) (tr_valid (exName_valid hs')) ih' (N.eMul s s' hs hs')
      (by set_tac) (by set_tac)

/-- The case analysis for terms of arity one. -/
theorem term_induction₁ {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (hbvar : P (^#(0 : V))) (hvar : ∀ i : V, P (^&i)) (hzero : P (zeroT : V))
    (hsucc : ∀ s : V, IsSemiterm PA194PAeq.language 1 s → P s → P (succT s))
    (hadd : ∀ s s' : V, IsSemiterm PA194PAeq.language 1 s → IsSemiterm PA194PAeq.language 1 s' →
      P s → P s' → P (addT s s'))
    (hmul : ∀ s s' : V, IsSemiterm PA194PAeq.language 1 s → IsSemiterm PA194PAeq.language 1 s' →
      P s → P s' → P (mulT s s')) :
    ∀ a : V, IsSemiterm PA194PAeq.language 1 a → P a := by
  apply IsSemiterm.induction 𝚺 hP
  · intro z hz
    have hz0 : z = 0 := by simpa using hz
    subst hz0
    exact hbvar
  · exact hvar
  · intro k f v hf hv ih
    rcases (PA194PAeq.source_functions k f).mp hf with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,htwo⟩
    · have hv0 : v = 0 := len_zero_iff_eq_nil.mp hv.isUTerm.lh.symm
      subst v
      exact hzero
    · obtain ⟨a,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.isUTerm.lh.symm
      have ha : IsSemiterm PA194PAeq.language 1 a := by
        simpa using hv.nth (show (0 : V) < 1 by simp)
      exact hsucc a ha (by simpa using ih 0 (by simp))
    · obtain ⟨a,b,rfl⟩ := eq_doubleton_of_len_eq_two.mp hv.isUTerm.lh.symm
      have ha : IsSemiterm PA194PAeq.language 1 a := by
        simpa using hv.nth (show (0 : V) < 2 by simp)
      have hb : IsSemiterm PA194PAeq.language 1 b := by
        simpa using hv.nth (show (1 : V) < 2 by simp)
      have iha : P a := by simpa using ih 0 (by simp)
      have ihb : P b := by simpa using ih 1 (by simp)
      rcases htwo with rfl | rfl
      · exact hadd a b ha hb iha ihb
      · exact hmul a b ha hb iha ihb

/-- Names transfer along a substitution, in the direction given by the two terms `u` and `w`
that are substituted, once names transfer from `u` to `w`. -/
theorem nameSubst (N : NameFacts (V := V) T) {u w E : V}
    (hu : IsSemiterm PA194PAeq.language 0 u) (hw : IsSemiterm PA194PAeq.language 0 w)
    (hE : IsFormula SourceL E)
    (hbase : GDerivable T (insert (neg SourceL E) (insert (tr (nameAll u w)) (∅ : V)))) :
    ∀ a : V, IsSemiterm PA194PAeq.language 1 a →
      GDerivable T (insert (neg SourceL E) (insert (tr (nameAll (sb u a) (sb w a))) (∅ : V))) := by
  have hnE : IsFormula SourceL (neg SourceL E) := IsSemiformula.neg_iff.mpr hE
  have hP : 𝚺₁-Predicate (fun a : V =>
      GDerivable T (insert (neg SourceL E) (insert (tr (nameAll (sb u a) (sb w a))) (∅ : V)))) := by
    unfold GDerivable sb
    definability
  apply term_induction₁ hP
  · rw [sb_bvar, sb_bvar]
    exact hbase
  · intro i
    rw [sb_fvar, sb_fvar]
    exact GDerivable.wk (fs_cons hnE (fs_cons (tr_valid (nameAll_valid (by simp) (by simp))) fs_nil))
      (by set_tac) (N.nRefl (^&i) (by simp))
  · rw [sb_zero, sb_zero]
    exact GDerivable.wk (fs_cons hnE (fs_cons (tr_valid (nameAll_valid zeroT_valid zeroT_valid))
      fs_nil)) (by set_tac) (N.nRefl zeroT zeroT_valid)
  · intro s hs ih
    have h1 := sb_valid hu hs
    have h2 := sb_valid hw hs
    rw [sb_succ hs, sb_succ hs]
    exact GDerivable.cut_wk (fs_cons hnE (fs_cons (tr_valid (nameAll_valid (succT_valid h1)
      (succT_valid h2))) fs_nil)) (tr_valid (nameAll_valid h1 h2)) ih (N.nSucc _ _ h1 h2)
      (by set_tac) (by set_tac)
  · intro s s' hs hs' ih ih'
    have h1 := sb_valid hu hs
    have h2 := sb_valid hw hs
    have h1' := sb_valid hu hs'
    have h2' := sb_valid hw hs'
    have hG := tr_valid (nameAll_valid (addT_valid h1 h1') (addT_valid h2 h2'))
    rw [sb_add hs hs', sb_add hs hs']
    refine GDerivable.cut_wk (fs_cons hnE (fs_cons hG fs_nil)) (tr_valid (nameAll_valid h1 h2)) ih ?_
      (by set_tac) (fun x hx => hx)
    exact GDerivable.cut_wk (fs_cons (IsSemiformula.neg_iff.mpr (tr_valid (nameAll_valid h1 h2)))
      (fs_cons hnE (fs_cons hG fs_nil))) (tr_valid (nameAll_valid h1' h2')) ih'
      (N.nAdd _ _ _ _ h1 h2 h1' h2') (by set_tac) (by set_tac)
  · intro s s' hs hs' ih ih'
    have h1 := sb_valid hu hs
    have h2 := sb_valid hw hs
    have h1' := sb_valid hu hs'
    have h2' := sb_valid hw hs'
    have hG := tr_valid (nameAll_valid (mulT_valid h1 h1') (mulT_valid h2 h2'))
    rw [sb_mul hs hs', sb_mul hs hs']
    refine GDerivable.cut_wk (fs_cons hnE (fs_cons hG fs_nil)) (tr_valid (nameAll_valid h1 h2)) ih ?_
      (by set_tac) (fun x hx => hx)
    exact GDerivable.cut_wk (fs_cons (IsSemiformula.neg_iff.mpr (tr_valid (nameAll_valid h1 h2)))
      (fs_cons hnE (fs_cons hG fs_nil))) (tr_valid (nameAll_valid h1' h2')) ih'
      (N.nMul _ _ _ _ h1 h2 h1' h2') (by set_tac) (by set_tac)

/-- Names transfer from `t` to `&c` when `&c = t`. -/
theorem name_term_to_var (N : NameFacts (V := V) T) {t : V} (c : V)
    (ht : IsSemiterm PA194PAeq.language 0 t) :
    GDerivable T (insert (neg SourceL (tr (peq (^&c) t)))
      (insert (tr (nameAll t (^&c))) (∅ : V))) := by
  have hc : IsSemiterm PA194PAeq.language 0 (^&c : V) := by simp
  have hE := tr_valid (peq_valid hc ht)
  exact GDerivable.cut_wk (fs_cons (IsSemiformula.neg_iff.mpr hE)
    (fs_cons (tr_valid (nameAll_valid ht hc)) fs_nil)) (tr_valid (uniq_valid ht))
    (uniq_all N t ht) (N.nameOfUniq t c ht) (by set_tac) (by set_tac)

/-- The term facts of the Leibniz lemma. -/
theorem termFacts_of_nameFacts (N : NameFacts (V := V) T) : TermFacts (V := V) T where
  atomPos := by
    intro a b t c ha hb ht
    have hc : IsSemiterm PA194PAeq.language 0 (^&c : V) := by simp
    have hE := tr_valid (peq_valid hc ht)
    have hnE : IsFormula SourceL (neg SourceL (tr (peq (^&c) t))) := IsSemiformula.neg_iff.mpr hE
    have hat := sb_valid ht ha
    have hbt := sb_valid ht hb
    have hac := sb_valid hc ha
    have hbc := sb_valid hc hb
    have h1 := nameSubst N ht hc hE (name_term_to_var N c ht) a ha
    have h2 := nameSubst N ht hc hE (name_term_to_var N c ht) b hb
    have h3 := N.atomTransfer (sb t a) (sb (^&c) a) (sb t b) (sb (^&c) b) hat hac hbt hbc
    have hX := tr_valid (peq_valid hat hbt)
    have hY := tr_valid (peq_valid hac hbc)
    have hNa := tr_valid (nameAll_valid hat hac)
    have hNb := tr_valid (nameAll_valid hbt hbc)
    unfold leibnizSeq
    rw [substs1_peq ha hb, substs1_peq ha hb]
    show GDerivable T (insert (neg SourceL (tr (peq (^&c) t)))
      (insert (neg SourceL (tr (peq (sb t a) (sb t b))))
        (insert (tr (peq (sb (^&c) a) (sb (^&c) b))) (∅ : V))))
    have hΔ : IsFormulaSet SourceL (insert (neg SourceL (tr (peq (^&c) t)))
        (insert (neg SourceL (tr (peq (sb t a) (sb t b))))
          (insert (tr (peq (sb (^&c) a) (sb (^&c) b))) (∅ : V)))) :=
      fs_cons hnE (fs_cons (IsSemiformula.neg_iff.mpr hX) (fs_cons hY fs_nil))
    refine GDerivable.cut_wk hΔ hNa h1 ?_ (by set_tac) (fun x hx => hx)
    exact GDerivable.cut_wk (fs_cons (IsSemiformula.neg_iff.mpr hNa) hΔ) hNb h2 h3
      (by set_tac) (by set_tac)
  atomNeg := by
    intro a b t c ha hb ht
    have hc : IsSemiterm PA194PAeq.language 0 (^&c : V) := by simp
    have hE := tr_valid (peq_valid hc ht)
    have hnE : IsFormula SourceL (neg SourceL (tr (peq (^&c) t))) := IsSemiformula.neg_iff.mpr hE
    have hat := sb_valid ht ha
    have hbt := sb_valid ht hb
    have hac := sb_valid hc ha
    have hbc := sb_valid hc hb
    have h1 := nameSubst N hc ht hE (N.nameOfEq t c ht) a ha
    have h2 := nameSubst N hc ht hE (N.nameOfEq t c ht) b hb
    have h3 := N.atomTransfer (sb (^&c) a) (sb t a) (sb (^&c) b) (sb t b) hac hat hbc hbt
    have hX := tr_valid (peq_valid hat hbt)
    have hY := tr_valid (peq_valid hac hbc)
    have hNa := tr_valid (nameAll_valid hac hat)
    have hNb := tr_valid (nameAll_valid hbc hbt)
    rw [substs1_peq ha hb, substs1_peq ha hb]
    show GDerivable T (insert (neg SourceL (tr (peq (^&c) t)))
      (insert (neg SourceL (tr (peq (sb (^&c) a) (sb (^&c) b))))
        (insert (tr (peq (sb t a) (sb t b))) (∅ : V))))
    have hΔ : IsFormulaSet SourceL (insert (neg SourceL (tr (peq (^&c) t)))
        (insert (neg SourceL (tr (peq (sb (^&c) a) (sb (^&c) b))))
          (insert (tr (peq (sb t a) (sb t b))) (∅ : V)))) :=
      fs_cons hnE (fs_cons (IsSemiformula.neg_iff.mpr hY) (fs_cons hX fs_nil))
    refine GDerivable.cut_wk hΔ hNa h1 ?_ (by set_tac) (fun x hx => hx)
    exact GDerivable.cut_wk (fs_cons (IsSemiformula.neg_iff.mpr hNa) hΔ) hNb h2 h3
      (by set_tac) (by set_tac)
  totEq := fun t ht => exName_all N t ht

#print axioms uniq_all
#print axioms exName_all
#print axioms nameSubst
#print axioms termFacts_of_nameFacts
end generic
end PA194GuardedCompiler
