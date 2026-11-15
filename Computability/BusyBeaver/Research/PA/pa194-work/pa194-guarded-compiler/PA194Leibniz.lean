import PA194TrCompile
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The translated Leibniz lemma and existential introduction at a term

From three facts about terms (`TermFacts`) the guarded calculus derives, for every internal
formula `p` of arity one, term `t` and free variable `c`,

  `¬ tr(&c = t), ¬ tr(p[t]), tr(p[&c])`.

Opening a quantifier of `p` shifts the free variables of `t`, so the induction is over the
triples `(p, t, c)` with the formula complexity as measure. The existential introduction at
an arbitrary term follows by eliminating `c` against `tr(∃x. x = t)`.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher

/-- Membership goals between explicit finite sets. -/
macro "set_tac" : tactic =>
  `(tactic| (intro x hx
             simp only [mem_bitInsert_iff, mem_singleton_iff, not_mem_empty, or_false] at hx ⊢
             tauto))

section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem fs_cons {a s : V} (ha : IsFormula SourceL a) (hs : IsFormulaSet SourceL s) :
    IsFormulaSet SourceL (insert a s) := IsFormulaSet.insert_iff.mpr ⟨ha,hs⟩
theorem fs_nil : IsFormulaSet SourceL (∅ : V) := IsFormulaSet.empty

/-! ### The equality atom of the arithmetic language -/

/-- The equality atom of the arithmetic language. -/
noncomputable def peq (a b : V) : V := ^rel (2 : V) 0 (?[a,b] : V)
instance peq_definable : 𝚺₁-Function₂ (peq : V → V → V) := by
  show 𝚺₁-Function₂ (fun a b : V => ^rel (2 : V) 0 (?[a,b] : V))
  definability

theorem isRel_eq : PA194PAeq.language.IsRel (2 : V) 0 := by simp
theorem peq_valid {n a b : V} (ha : IsSemiterm PA194PAeq.language n a)
    (hb : IsSemiterm PA194PAeq.language n b) : IsSemiformula PA194PAeq.language n (peq a b) := by
  unfold peq
  exact IsSemiformula.rel.mpr ⟨isRel_eq,by simp [ha,hb]⟩
theorem substs1_peq {a b t : V} (ha : IsSemiterm PA194PAeq.language 1 a)
    (hb : IsSemiterm PA194PAeq.language 1 b) :
    substs1 PA194PAeq.language t (peq a b) =
      peq (termSubst PA194PAeq.language (?[t] : V) a) (termSubst PA194PAeq.language (?[t] : V) b) := by
  have hv : IsUTermVec PA194PAeq.language 2 (?[a,b] : V) := by simp [ha.isUTerm,hb.isUTerm]
  show subst PA194PAeq.language (?[t] : V) (^rel (2 : V) 0 (?[a,b] : V)) =
    ^rel (2 : V) 0 (?[termSubst PA194PAeq.language (?[t] : V) a,
      termSubst PA194PAeq.language (?[t] : V) b] : V)
  rw [substs_rel isRel_eq hv, termSubstVec_cons₂ ha.isUTerm hb.isUTerm]
theorem shift_peq {n a b : V} (ha : IsSemiterm PA194PAeq.language n a)
    (hb : IsSemiterm PA194PAeq.language n b) :
    shift PA194PAeq.language (peq a b) =
      peq (termShift PA194PAeq.language a) (termShift PA194PAeq.language b) := by
  have hv : IsUTermVec PA194PAeq.language 2 (?[a,b] : V) := by simp [ha.isUTerm,hb.isUTerm]
  show shift PA194PAeq.language (^rel (2 : V) 0 (?[a,b] : V)) =
    ^rel (2 : V) 0 (?[termShift PA194PAeq.language a,termShift PA194PAeq.language b] : V)
  rw [shift_rel isRel_eq hv, termShiftVec_cons₂ ha.isUTerm hb.isUTerm]
theorem bShift_valid {t : V} (ht : IsSemiterm PA194PAeq.language 0 t) :
    IsSemiterm PA194PAeq.language 1 (termBShift PA194PAeq.language t) := by
  simpa using IsSemiterm.termBShift ht
theorem free_peq_bvar {t : V} (ht : IsSemiterm PA194PAeq.language 0 t) :
    free PA194PAeq.language (peq (^#(0 : V)) (termBShift PA194PAeq.language t)) =
      peq (^&(0 : V)) (termShift PA194PAeq.language t) := by
  have h0 : IsSemiterm PA194PAeq.language 1 (^#(0 : V)) := by simp
  show substs1 PA194PAeq.language (^&(0 : V))
      (shift PA194PAeq.language (peq (^#(0 : V)) (termBShift PA194PAeq.language t))) =
    peq (^&(0 : V)) (termShift PA194PAeq.language t)
  rw [shift_peq h0 (bShift_valid ht), termShift_bvar, ← termBShift_termShift ht,
    substs1_peq h0 (bShift_valid ht.termShift), termSubst_bvar,
    substs_cons_bShift ht.termShift, substs_nil ht.termShift]
  simp

/-! ### Substitution and shift in the arithmetic language -/

theorem shift_substs1 {p t : V} (hp : IsSemiformula PA194PAeq.language 1 p)
    (ht : IsSemiterm PA194PAeq.language 0 t) :
    shift PA194PAeq.language (substs1 PA194PAeq.language t p) =
      substs1 PA194PAeq.language (termShift PA194PAeq.language t) (shift PA194PAeq.language p) := by
  have hw : IsSemitermVec PA194PAeq.language 1 0 (?[t] : V) := by simp [ht]
  show shift PA194PAeq.language (subst PA194PAeq.language (?[t] : V) p) =
    subst PA194PAeq.language (?[termShift PA194PAeq.language t] : V) (shift PA194PAeq.language p)
  rw [shift_substs hp hw, termShiftVec_cons₁ ht.isUTerm]
theorem qVecA_singleton {t : V} (ht : IsSemiterm PA194PAeq.language 0 t) :
    qVec PA194PAeq.language (?[t] : V) = (?[^#(0 : V), termBShift PA194PAeq.language t] : V) := by
  have hl : len (?[t] : V) = 1 := by simp
  unfold qVec
  rw [hl, termBShiftVec_cons₁ ht.isUTerm]
theorem qVecA_singleton_valid {t : V} (ht : IsSemiterm PA194PAeq.language 0 t) :
    IsSemitermVec PA194PAeq.language 2 1 (qVec PA194PAeq.language (?[t] : V)) := by
  rw [qVecA_singleton ht]
  simp [bShift_valid ht]
/-- Opening the quantified variable of `q[#0, t]` is `(free1 q)[shift t]`. -/
theorem free_subst_qVec {q t : V} (hq : IsSemiformula PA194PAeq.language 2 q)
    (ht : IsSemiterm PA194PAeq.language 0 t) :
    free PA194PAeq.language (subst PA194PAeq.language (qVec PA194PAeq.language (?[t] : V)) q) =
      substs1 PA194PAeq.language (termShift PA194PAeq.language t) (free1 PA194PAeq.language q) := by
  have hb : IsSemiterm PA194PAeq.language 1 (termBShift PA194PAeq.language t) := bShift_valid ht
  have hbs : IsSemiterm PA194PAeq.language 1
      (termBShift PA194PAeq.language (termShift PA194PAeq.language t)) := bShift_valid ht.termShift
  have hw1 : IsSemitermVec PA194PAeq.language 2 1
      (?[^#(0 : V), termBShift PA194PAeq.language t] : V) := by simp [hb]
  have hw1s : IsSemitermVec PA194PAeq.language 2 1
      (?[^#(0 : V), termBShift PA194PAeq.language (termShift PA194PAeq.language t)] : V) := by
    simp [hbs]
  have h0 : IsSemitermVec PA194PAeq.language 1 0 (?[^&(0 : V)] : V) := by simp
  have hts : IsSemitermVec PA194PAeq.language 1 0 (?[termShift PA194PAeq.language t] : V) := by
    simp [ht]
  have hf1 : IsSemitermVec PA194PAeq.language 2 1 (?[^&(0 : V), ^#(0 : V)] : V) := by simp
  have hb0 : IsUTerm PA194PAeq.language (^#(0 : V)) := by simp
  have hf0 : IsUTerm PA194PAeq.language (^&(0 : V)) := by simp
  rw [qVecA_singleton ht]
  show subst PA194PAeq.language (?[^&(0 : V)] : V)
      (shift PA194PAeq.language
        (subst PA194PAeq.language (?[^#(0 : V), termBShift PA194PAeq.language t] : V) q)) =
    subst PA194PAeq.language (?[termShift PA194PAeq.language t] : V)
      (subst PA194PAeq.language (?[^&(0 : V), ^#(0 : V)] : V) (shift PA194PAeq.language q))
  rw [shift_substs hq hw1, termShiftVec_cons₂ hb0 hb.isUTerm, termShift_bvar,
    ← termBShift_termShift ht, substs_substs hq.shift h0 hw1s, substs_substs hq.shift hts hf1,
    termSubstVec_cons₂ hb0 hbs.isUTerm, termSubstVec_cons₂ hf0 hb0, termSubst_bvar,
    substs_cons_bShift ht.termShift, substs_nil ht.termShift, termSubst_fvar, termSubst_bvar]
  simp

theorem substs1_all {q t : V} (hq : IsSemiformula PA194PAeq.language 2 q) :
    substs1 PA194PAeq.language t (^∀ q) =
      ^∀ (subst PA194PAeq.language (qVec PA194PAeq.language (?[t] : V)) q) := by
  show subst PA194PAeq.language (?[t] : V) (^∀ q) = _
  rw [substs_all hq.isUFormula]
theorem substs1_exs {q t : V} (hq : IsSemiformula PA194PAeq.language 2 q) :
    substs1 PA194PAeq.language t (^∃ q) =
      ^∃ (subst PA194PAeq.language (qVec PA194PAeq.language (?[t] : V)) q) := by
  show subst PA194PAeq.language (?[t] : V) (^∃ q) = _
  rw [substs_ex hq.isUFormula]
theorem substs1_andA {p q t : V} (hp : IsSemiformula PA194PAeq.language 1 p)
    (hq : IsSemiformula PA194PAeq.language 1 q) :
    substs1 PA194PAeq.language t (p ^⋏ q) =
      substs1 PA194PAeq.language t p ^⋏ substs1 PA194PAeq.language t q := by
  show subst PA194PAeq.language (?[t] : V) (p ^⋏ q) = _
  rw [substs_and hp.isUFormula hq.isUFormula]
  rfl
theorem substs1_orA {p q t : V} (hp : IsSemiformula PA194PAeq.language 1 p)
    (hq : IsSemiformula PA194PAeq.language 1 q) :
    substs1 PA194PAeq.language t (p ^⋎ q) =
      substs1 PA194PAeq.language t p ^⋎ substs1 PA194PAeq.language t q := by
  show subst PA194PAeq.language (?[t] : V) (p ^⋎ q) = _
  rw [substs_or hp.isUFormula hq.isUFormula]
  rfl
theorem substs1_negA {p t : V} (hp : IsSemiformula PA194PAeq.language 1 p)
    (ht : IsSemiterm PA194PAeq.language 0 t) :
    substs1 PA194PAeq.language t (neg PA194PAeq.language p) =
      neg PA194PAeq.language (substs1 PA194PAeq.language t p) := by
  have hw : IsSemitermVec PA194PAeq.language 1 0 (?[t] : V) := by simp [ht]
  show subst PA194PAeq.language (?[t] : V) (neg PA194PAeq.language p) = _
  rw [substs_neg hp hw]
  rfl

/-! ### Negation, shift and opening in the source language -/

theorem neg_all_rel {B : V} (hB : IsSemiformula SourceL 1 B) :
    neg SourceL (^∀ (guardBody ^⋎ B)) = ^∃ (domainCode (^#(0 : V)) ^⋏ neg SourceL B) := by
  rw [neg_all (IsSemiformula.or.mpr ⟨guardBody_valid,hB⟩).isUFormula,
    neg_or guardBody_valid.isUFormula hB.isUFormula]
  unfold guardBody
  rw [IsUFormula.neg_neg domainBody_valid.isUFormula]
theorem neg_ex_rel {B : V} (hB : IsSemiformula SourceL 1 B) :
    neg SourceL (^∃ (domainCode (^#(0 : V)) ^⋏ B)) = ^∀ (guardBody ^⋎ neg SourceL B) := by
  show neg SourceL (^∃ (domainCode (^#(0 : V)) ^⋏ B)) =
    ^∀ (neg SourceL (domainCode (^#(0 : V))) ^⋎ neg SourceL B)
  rw [neg_ex (IsSemiformula.and.mpr ⟨domainBody_valid,hB⟩).isUFormula,
    neg_and domainBody_valid.isUFormula hB.isUFormula]
theorem substs1_negS {X u : V} (hX : IsSemiformula SourceL 1 X) (hu : IsSemiterm SourceL 0 u) :
    substs1 SourceL u (neg SourceL X) = neg SourceL (substs1 SourceL u X) := by
  have hw : IsSemitermVec SourceL 1 0 (?[u] : V) := by simp [hu]
  show subst SourceL (?[u] : V) (neg SourceL X) = _
  rw [substs_neg hX hw]
  rfl
theorem free_negS {X : V} (hX : IsSemiformula SourceL 1 X) :
    free SourceL (neg SourceL X) = neg SourceL (free SourceL X) := by
  show substs1 SourceL (^&(0 : V)) (shift SourceL (neg SourceL X)) = _
  rw [shift_neg hX, substs1_negS hX.shift (by simp)]
  rfl
theorem shift_neg_tr {φ : V} (hφ : IsSemiformula PA194PAeq.language 0 φ) :
    shift SourceL (neg SourceL (tr φ)) = neg SourceL (tr (shift PA194PAeq.language φ)) := by
  rw [shift_neg (tr_valid hφ), tr_shift hφ]

/-! ### The Leibniz sequent -/

/-- `¬ tr(&c = t), ¬ tr(p[t]), tr(p[&c])`. -/
noncomputable def leibnizSeq (p t c : V) : V :=
  insert (neg SourceL (tr (peq (^&c) t)))
    (insert (neg SourceL (tr (substs1 PA194PAeq.language t p)))
      (insert (tr (substs1 PA194PAeq.language (^&c) p)) (∅ : V)))
instance leibnizSeq_definable : 𝚺₁-Function₃ (leibnizSeq : V → V → V → V) := by
  show 𝚺₁-Function₃ (fun p t c : V => insert (neg SourceL (tr (peq (^&c) t)))
    (insert (neg SourceL (tr (substs1 PA194PAeq.language t p)))
      (insert (tr (substs1 PA194PAeq.language (^&c) p)) (∅ : V))))
  definability

variable (T : Theory SourceL) [T.Δ₁]

/-- The facts about terms that the Leibniz lemma and the existential rule rest on. -/
structure TermFacts : Prop where
  /-- Leibniz for a positive equality atom. -/
  atomPos : ∀ a b t c : V, IsSemiterm PA194PAeq.language 1 a → IsSemiterm PA194PAeq.language 1 b →
    IsSemiterm PA194PAeq.language 0 t → GDerivable T (leibnizSeq (peq a b) t c)
  /-- Leibniz for a negative equality atom. -/
  atomNeg : ∀ a b t c : V, IsSemiterm PA194PAeq.language 1 a → IsSemiterm PA194PAeq.language 1 b →
    IsSemiterm PA194PAeq.language 0 t →
    GDerivable T (insert (neg SourceL (tr (peq (^&c) t)))
      (insert (neg SourceL (tr (substs1 PA194PAeq.language (^&c) (peq a b))))
        (insert (tr (substs1 PA194PAeq.language t (peq a b))) (∅ : V))))
  /-- Every term is equal to an element of the domain. -/
  totEq : ∀ t : V, IsSemiterm PA194PAeq.language 0 t →
    GDerivable T (insert (tr (^∃ (peq (^#(0 : V)) (termBShift PA194PAeq.language t)))) (∅ : V))

/-- The statement of the Leibniz lemma at a coded triple. -/
def LeibnizAt (x : V) : Prop :=
  IsSemiformula PA194PAeq.language 1 (π₁ x) → IsSemiterm PA194PAeq.language 0 (π₁ (π₂ x)) →
    ∃ n, Derivable T (guards n ∪ leibnizSeq (π₁ x) (π₁ (π₂ x)) (π₂ (π₂ x)))
noncomputable def leibnizMeasure (x : V) : V := formulaComplexity PA194PAeq.language (π₁ x)
noncomputable def leibnizBound (x : V) : V :=
  max x ⟪free1 PA194PAeq.language (π₂ (π₁ x - 1)),
    termShift PA194PAeq.language (π₁ (π₂ x)), π₂ (π₂ x) + 1⟫

variable {T}

theorem leibniz_aux (F : TermFacts (V := V) T) : ∀ x : V, LeibnizAt T x := by
  have hm : 𝚺₁-Function₁ (leibnizMeasure : V → V) := by unfold leibnizMeasure; definability
  have hf : 𝚺₁-Function₁ (leibnizBound : V → V) := by unfold leibnizBound; definability
  have hP : 𝚺₁-Predicate (LeibnizAt T : V → Prop) := by unfold LeibnizAt; definability
  apply measured_bounded_sigma1_order_induction hm hf hP
  intro x ih
  obtain ⟨p,t,c,rfl⟩ : ∃ p t c : V, x = ⟪p, t, c⟫ := ⟨π₁ x,π₁ (π₂ x),π₂ (π₂ x),by simp⟩
  unfold LeibnizAt
  simp only [pi₁_pair, pi₂_pair]
  intro hp ht
  show GDerivable T (leibnizSeq p t c)
  have IH : ∀ p' t' c' : V, ⟪p', t', c'⟫ ≤ leibnizBound ⟪p, t, c⟫ →
      formulaComplexity PA194PAeq.language p' < formulaComplexity PA194PAeq.language p →
      IsSemiformula PA194PAeq.language 1 p' → IsSemiterm PA194PAeq.language 0 t' →
      GDerivable T (leibnizSeq p' t' c') := by
    intro p' t' c' hle hlt hp' ht'
    have h := ih ⟪p', t', c'⟫ hle (by simpa [leibnizMeasure] using hlt)
    unfold LeibnizAt at h
    simp only [pi₁_pair, pi₂_pair] at h
    exact h hp' ht'
  have hsub : ∀ p' : V, p' ≤ p → ⟪p', t, c⟫ ≤ leibnizBound ⟪p, t, c⟫ := fun p' h =>
    le_trans (pair_le_pair_left h _) (le_max_left _ _)
  have hc : IsSemiterm PA194PAeq.language 0 (^&c : V) := by simp
  have hE : IsFormula SourceL (tr (peq (^&c) t)) := tr_valid (peq_valid hc ht)
  have hnE : IsFormula SourceL (neg SourceL (tr (peq (^&c) t))) := IsSemiformula.neg_iff.mpr hE
  have hAt : IsFormula SourceL (tr (substs1 PA194PAeq.language t p)) :=
    tr_valid (IsSemiformula.substs1 ht hp)
  have hAc : IsFormula SourceL (tr (substs1 PA194PAeq.language (^&c) p)) :=
    tr_valid (IsSemiformula.substs1 hc hp)
  have hΔ : IsFormulaSet SourceL (leibnizSeq p t c) :=
    fs_cons hnE (fs_cons (IsSemiformula.neg_iff.mpr hAt) (fs_cons hAc fs_nil))
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩
      | rfl | rfl
      | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩
      | ⟨q, h₁, rfl⟩ | ⟨q, h₁, rfl⟩)
  · -- positive atom
    rcases (PA194PAeq.source_relations k R).mp hR with ⟨rfl,rfl⟩
    obtain ⟨a,b,rfl⟩ := eq_doubleton_of_len_eq_two.mp hv.isUTerm.lh.symm
    have ha : IsSemiterm PA194PAeq.language 1 a := by simpa using hv.nth (show (0 : V) < 2 by simp)
    have hb : IsSemiterm PA194PAeq.language 1 b := by simpa using hv.nth (show (1 : V) < 2 by simp)
    exact F.atomPos a b t c ha hb ht
  · -- negative atom
    rcases (PA194PAeq.source_relations k R).mp hR with ⟨rfl,rfl⟩
    obtain ⟨a,b,rfl⟩ := eq_doubleton_of_len_eq_two.mp hv.isUTerm.lh.symm
    have ha : IsSemiterm PA194PAeq.language 1 a := by simpa using hv.nth (show (0 : V) < 2 by simp)
    have hb : IsSemiterm PA194PAeq.language 1 b := by simpa using hv.nth (show (1 : V) < 2 by simp)
    have hab : IsSemiformula PA194PAeq.language 1 (peq a b) := peq_valid ha hb
    have hn : (^nrel (2 : V) 0 (?[a,b] : V)) = neg PA194PAeq.language (peq a b) :=
      (neg_rel isRel_eq hv.isUTerm).symm
    have hXt := IsSemiformula.substs1 ht hab
    have hXc := IsSemiformula.substs1 hc hab
    unfold leibnizSeq
    rw [hn, substs1_negA hab ht, substs1_negA hab hc, tr_neg hXt, tr_neg hXc,
      IsUFormula.neg_neg (tr_valid hXt).isUFormula]
    refine GDerivable.wk (fs_cons hnE (fs_cons (tr_valid hXt)
      (fs_cons (IsSemiformula.neg_iff.mpr (tr_valid hXc)) fs_nil))) ?_ (F.atomNeg a b t c ha hb ht)
    set_tac
  · -- verum
    have h1 : substs1 PA194PAeq.language (^&c) (^⊤ : V) = ^⊤ := by simp [substs1]
    unfold leibnizSeq at hΔ ⊢
    rw [h1, tr_verum] at hΔ ⊢
    exact GDerivable.verum hΔ (by simp)
  · -- falsum
    have h1 : substs1 PA194PAeq.language t (^⊥ : V) = ^⊥ := by simp [substs1]
    unfold leibnizSeq at hΔ ⊢
    rw [h1, tr_falsum, neg_falsum] at hΔ ⊢
    exact GDerivable.verum hΔ (by simp)
  · -- conjunction
    have hA₁ := IsSemiformula.substs1 ht h₁
    have hA₂ := IsSemiformula.substs1 ht h₂
    have hC₁ := IsSemiformula.substs1 hc h₁
    have hC₂ := IsSemiformula.substs1 hc h₂
    have ih₁ := IH p₁ t c (hsub p₁ (le_of_lt (lt_qqAnd_left p₁ p₂)))
      (by simp [h₁.isUFormula,h₂.isUFormula]) h₁ ht
    have ih₂ := IH p₂ t c (hsub p₂ (le_of_lt (lt_qqAnd_right p₁ p₂)))
      (by simp [h₁.isUFormula,h₂.isUFormula]) h₂ ht
    unfold leibnizSeq at hΔ ih₁ ih₂ ⊢
    rw [substs1_andA h₁ h₂, substs1_andA h₁ h₂, tr_and hA₁ hA₂, tr_and hC₁ hC₂,
      neg_and (tr_valid hA₁).isUFormula (tr_valid hA₂).isUFormula] at hΔ ⊢
    have hnA₁ : IsFormula SourceL (neg SourceL (tr (substs1 PA194PAeq.language t p₁))) :=
      IsSemiformula.neg_iff.mpr (tr_valid hA₁)
    have hnA₂ : IsFormula SourceL (neg SourceL (tr (substs1 PA194PAeq.language t p₂))) :=
      IsSemiformula.neg_iff.mpr (tr_valid hA₂)
    refine GDerivable.or_m (p := neg SourceL (tr (substs1 PA194PAeq.language t p₁)))
      (q := neg SourceL (tr (substs1 PA194PAeq.language t p₂))) (by simp) ?_
    refine GDerivable.and_m (p := tr (substs1 PA194PAeq.language (^&c) p₁))
      (q := tr (substs1 PA194PAeq.language (^&c) p₂)) (by simp) ?_ ?_
    · exact GDerivable.wk (fs_cons (tr_valid hC₁) (fs_cons hnA₁ (fs_cons hnA₂ hΔ)))
        (by set_tac) ih₁
    · exact GDerivable.wk (fs_cons (tr_valid hC₂) (fs_cons hnA₁ (fs_cons hnA₂ hΔ)))
        (by set_tac) ih₂
  · -- disjunction
    have hA₁ := IsSemiformula.substs1 ht h₁
    have hA₂ := IsSemiformula.substs1 ht h₂
    have hC₁ := IsSemiformula.substs1 hc h₁
    have hC₂ := IsSemiformula.substs1 hc h₂
    have ih₁ := IH p₁ t c (hsub p₁ (le_of_lt (lt_qqOr_left p₁ p₂)))
      (by simp [h₁.isUFormula,h₂.isUFormula]) h₁ ht
    have ih₂ := IH p₂ t c (hsub p₂ (le_of_lt (lt_qqOr_right p₁ p₂)))
      (by simp [h₁.isUFormula,h₂.isUFormula]) h₂ ht
    unfold leibnizSeq at hΔ ih₁ ih₂ ⊢
    rw [substs1_orA h₁ h₂, substs1_orA h₁ h₂, tr_or hA₁ hA₂, tr_or hC₁ hC₂,
      neg_or (tr_valid hA₁).isUFormula (tr_valid hA₂).isUFormula] at hΔ ⊢
    have hnA₁ : IsFormula SourceL (neg SourceL (tr (substs1 PA194PAeq.language t p₁))) :=
      IsSemiformula.neg_iff.mpr (tr_valid hA₁)
    have hnA₂ : IsFormula SourceL (neg SourceL (tr (substs1 PA194PAeq.language t p₂))) :=
      IsSemiformula.neg_iff.mpr (tr_valid hA₂)
    refine GDerivable.or_m (p := tr (substs1 PA194PAeq.language (^&c) p₁))
      (q := tr (substs1 PA194PAeq.language (^&c) p₂)) (by simp) ?_
    refine GDerivable.and_m (p := neg SourceL (tr (substs1 PA194PAeq.language t p₁)))
      (q := neg SourceL (tr (substs1 PA194PAeq.language t p₂))) (by simp) ?_ ?_
    · exact GDerivable.wk (fs_cons hnA₁ (fs_cons (tr_valid hC₁) (fs_cons (tr_valid hC₂) hΔ)))
        (by set_tac) ih₁
    · exact GDerivable.wk (fs_cons hnA₂ (fs_cons (tr_valid hC₁) (fs_cons (tr_valid hC₂) hΔ)))
        (by set_tac) ih₂
  · -- universal quantifier
    have hq : IsSemiformula PA194PAeq.language 2 q := by simpa [one_add_one_eq_two] using h₁
    have hq' : π₂ ((^∀ q : V) - 1) = q := by simp [qqAll]
    have hrt : IsSemiformula PA194PAeq.language 1
        (subst PA194PAeq.language (qVec PA194PAeq.language (?[t] : V)) q) :=
      hq.subst (qVecA_singleton_valid ht)
    have hrc : IsSemiformula PA194PAeq.language 1
        (subst PA194PAeq.language (qVec PA194PAeq.language (?[^&c] : V)) q) :=
      hq.subst (qVecA_singleton_valid hc)
    have hBt := trBody_valid hrt
    have hBc := trBody_valid hrc
    have hBt' := trBody_valid hrt.shift
    have hfq : IsSemiformula PA194PAeq.language 1 (free1 PA194PAeq.language q) := hq.free1
    have ih := IH (free1 PA194PAeq.language q) (termShift PA194PAeq.language t) (c + 1)
      (by unfold leibnizBound; simp only [pi₁_pair, pi₂_pair, hq']; exact le_max_right _ _)
      (by simp [fomulaComplexity_free1 hq, hq.isUFormula]) hfq ht.termShift
    -- the shifted pieces
    have e1 : shift SourceL (neg SourceL (tr (peq (^&c) t))) =
        neg SourceL (tr (peq (^&(c+1)) (termShift PA194PAeq.language t))) := by
      rw [shift_neg_tr (peq_valid hc ht), shift_peq hc ht, termShift_fvar]
    have e2 : shift SourceL (^∃ (domainCode (^#(0 : V)) ^⋏ neg SourceL (trBody
          (subst PA194PAeq.language (qVec PA194PAeq.language (?[t] : V)) q)))) =
        ^∃ (domainCode (^#(0 : V)) ^⋏ neg SourceL (trBody (shift PA194PAeq.language
          (subst PA194PAeq.language (qVec PA194PAeq.language (?[t] : V)) q)))) := by
      rw [← neg_all_rel hBt, ← tr_all hrt, shift_neg_tr (IsSemiformula.all.mpr (by simpa using hrt)),
        shift_all hrt.isUFormula, tr_all hrt.shift, neg_all_rel hBt']
    have e3 : substs1 SourceL (^&(0 : V)) (neg SourceL (trBody (shift PA194PAeq.language
          (subst PA194PAeq.language (qVec PA194PAeq.language (?[t] : V)) q)))) =
        neg SourceL (tr (substs1 PA194PAeq.language (termShift PA194PAeq.language t)
          (free1 PA194PAeq.language q))) := by
      rw [substs1_negS hBt' (by simp), ← tr_substs1_fvar hrt.shift (0 : V), ← free_subst_qVec hq ht]
      rfl
    have e4 : free SourceL (trBody
          (subst PA194PAeq.language (qVec PA194PAeq.language (?[^&c] : V)) q)) =
        tr (substs1 PA194PAeq.language (^&(c+1)) (free1 PA194PAeq.language q)) := by
      rw [← tr_free hrc, free_subst_qVec hq hc, termShift_fvar]
    unfold leibnizSeq at hΔ ih ⊢
    rw [substs1_all hq, substs1_all hq, tr_all hrt, tr_all hrc, neg_all_rel hBt] at hΔ ⊢
    refine GDerivable.all_rel hBc (by simp) ?_
    rw [mem_setShift_insert, mem_setShift_insert, mem_setShift_insert, setShift_empty, e1, e2, e4]
    have hall' : IsFormula SourceL (shift SourceL (^∀ (guardBody ^⋎ trBody
        (subst PA194PAeq.language (qVec PA194PAeq.language (?[^&c] : V)) q)))) := by
      have h := (IsFormulaSet.insert_iff.mp (IsFormulaSet.insert_iff.mp hΔ).2).2
      exact ((IsFormulaSet.insert_iff.mp h).1).shift
    have hex' : IsFormula SourceL (^∃ (domainCode (^#(0 : V)) ^⋏ neg SourceL (trBody
        (shift PA194PAeq.language
          (subst PA194PAeq.language (qVec PA194PAeq.language (?[t] : V)) q))))) := by
      simpa using IsSemiformula.and.mpr ⟨domainBody_valid (V := V),IsSemiformula.neg_iff.mpr hBt'⟩
    have hE' : IsFormula SourceL (neg SourceL (tr (peq (^&(c+1))
        (termShift PA194PAeq.language t)))) :=
      IsSemiformula.neg_iff.mpr (tr_valid (peq_valid (by simp) ht.termShift))
    have hXt : IsFormula SourceL (tr (substs1 PA194PAeq.language (termShift PA194PAeq.language t)
        (free1 PA194PAeq.language q))) := tr_valid (IsSemiformula.substs1 ht.termShift hfq)
    have hXc : IsFormula SourceL (tr (substs1 PA194PAeq.language (^&(c+1))
        (free1 PA194PAeq.language q))) := tr_valid (IsSemiformula.substs1 (by simp) hfq)
    refine GDerivable.ex_rel (IsSemiformula.neg_iff.mpr hBt') (by simp) (0 : V) ?_
    rw [e3]
    exact GDerivable.wk (fs_cons (IsSemiformula.neg_iff.mpr hXt) (fs_cons hXc (fs_cons hE'
      (fs_cons hex' (fs_cons hall' fs_nil))))) (by set_tac) ih
  · -- existential quantifier
    have hq : IsSemiformula PA194PAeq.language 2 q := by simpa [one_add_one_eq_two] using h₁
    have hq' : π₂ ((^∃ q : V) - 1) = q := by simp [qqExs]
    have hrt : IsSemiformula PA194PAeq.language 1
        (subst PA194PAeq.language (qVec PA194PAeq.language (?[t] : V)) q) :=
      hq.subst (qVecA_singleton_valid ht)
    have hrc : IsSemiformula PA194PAeq.language 1
        (subst PA194PAeq.language (qVec PA194PAeq.language (?[^&c] : V)) q) :=
      hq.subst (qVecA_singleton_valid hc)
    have hBt := trBody_valid hrt
    have hBc := trBody_valid hrc
    have hBc' := trBody_valid hrc.shift
    have hfq : IsSemiformula PA194PAeq.language 1 (free1 PA194PAeq.language q) := hq.free1
    have ih := IH (free1 PA194PAeq.language q) (termShift PA194PAeq.language t) (c + 1)
      (by unfold leibnizBound; simp only [pi₁_pair, pi₂_pair, hq']; exact le_max_right _ _)
      (by simp [fomulaComplexity_free1 hq, hq.isUFormula]) hfq ht.termShift
    have e1 : shift SourceL (neg SourceL (tr (peq (^&c) t))) =
        neg SourceL (tr (peq (^&(c+1)) (termShift PA194PAeq.language t))) := by
      rw [shift_neg_tr (peq_valid hc ht), shift_peq hc ht, termShift_fvar]
    have e2 : shift SourceL (^∃ (domainCode (^#(0 : V)) ^⋏ trBody
          (subst PA194PAeq.language (qVec PA194PAeq.language (?[^&c] : V)) q))) =
        ^∃ (domainCode (^#(0 : V)) ^⋏ trBody (shift PA194PAeq.language
          (subst PA194PAeq.language (qVec PA194PAeq.language (?[^&c] : V)) q))) := by
      rw [← tr_exs hrc, ← tr_shift (IsSemiformula.exs.mpr (by simpa using hrc)),
        shift_exs hrc.isUFormula, tr_exs hrc.shift]
    have e3 : substs1 SourceL (^&(0 : V)) (trBody (shift PA194PAeq.language
          (subst PA194PAeq.language (qVec PA194PAeq.language (?[^&c] : V)) q))) =
        tr (substs1 PA194PAeq.language (^&(c+1)) (free1 PA194PAeq.language q)) := by
      rw [← tr_substs1_fvar hrc.shift (0 : V), ← termShift_fvar (L := PA194PAeq.language) c, ← free_subst_qVec hq hc]
      rfl
    have e4 : free SourceL (neg SourceL (trBody
          (subst PA194PAeq.language (qVec PA194PAeq.language (?[t] : V)) q))) =
        neg SourceL (tr (substs1 PA194PAeq.language (termShift PA194PAeq.language t)
          (free1 PA194PAeq.language q))) := by
      rw [free_negS hBt, ← tr_free hrt, free_subst_qVec hq ht]
    unfold leibnizSeq at hΔ ih ⊢
    rw [substs1_exs hq, substs1_exs hq, tr_exs hrt, tr_exs hrc, neg_ex_rel hBt] at hΔ ⊢
    refine GDerivable.all_rel (IsSemiformula.neg_iff.mpr hBt) (by simp) ?_
    rw [mem_setShift_insert, mem_setShift_insert, mem_setShift_insert, setShift_empty, e1, e2, e4]
    have hall' : IsFormula SourceL (shift SourceL (^∀ (guardBody ^⋎ neg SourceL (trBody
        (subst PA194PAeq.language (qVec PA194PAeq.language (?[t] : V)) q))))) := by
      have h := (IsFormulaSet.insert_iff.mp hΔ).2
      exact ((IsFormulaSet.insert_iff.mp h).1).shift
    have hex' : IsFormula SourceL (^∃ (domainCode (^#(0 : V)) ^⋏ trBody
        (shift PA194PAeq.language
          (subst PA194PAeq.language (qVec PA194PAeq.language (?[^&c] : V)) q)))) := by
      simpa using IsSemiformula.and.mpr ⟨domainBody_valid (V := V),hBc'⟩
    have hE' : IsFormula SourceL (neg SourceL (tr (peq (^&(c+1))
        (termShift PA194PAeq.language t)))) :=
      IsSemiformula.neg_iff.mpr (tr_valid (peq_valid (by simp) ht.termShift))
    have hXt : IsFormula SourceL (tr (substs1 PA194PAeq.language (termShift PA194PAeq.language t)
        (free1 PA194PAeq.language q))) := tr_valid (IsSemiformula.substs1 ht.termShift hfq)
    have hXc : IsFormula SourceL (tr (substs1 PA194PAeq.language (^&(c+1))
        (free1 PA194PAeq.language q))) := tr_valid (IsSemiformula.substs1 (by simp) hfq)
    refine GDerivable.ex_rel hBc' (by simp) (0 : V) ?_
    rw [e3]
    exact GDerivable.wk (fs_cons hXc (fs_cons (IsSemiformula.neg_iff.mpr hXt) (fs_cons hE'
      (fs_cons hall' (fs_cons hex' fs_nil))))) (by set_tac) ih

/-- The translated Leibniz lemma. -/
theorem leibniz (F : TermFacts (V := V) T) {p t : V} (c : V)
    (hp : IsSemiformula PA194PAeq.language 1 p) (ht : IsSemiterm PA194PAeq.language 0 t) :
    GDerivable T (leibnizSeq p t c) := by
  have h := leibniz_aux F ⟪p, t, c⟫
  unfold LeibnizAt at h
  simp only [pi₁_pair, pi₂_pair] at h
  exact h hp ht

/-- Existential introduction at an arbitrary term. -/
theorem witness_of_termFacts (F : TermFacts (V := V) T) {p t : V}
    (hp : IsSemiformula PA194PAeq.language 1 p) (ht : IsSemiterm PA194PAeq.language 0 t) :
    GDerivable T (insert (neg SourceL (tr (substs1 PA194PAeq.language t p))) ({tr (^∃ p)} : V)) := by
  have h0 : IsSemiterm PA194PAeq.language 1 (^#(0 : V)) := by simp
  have he : IsSemiformula PA194PAeq.language 1 (peq (^#(0 : V)) (termBShift PA194PAeq.language t)) :=
    peq_valid h0 (bShift_valid ht)
  have hBe := trBody_valid he
  have hA : IsSemiformula PA194PAeq.language 0 (substs1 PA194PAeq.language t p) :=
    IsSemiformula.substs1 ht hp
  have hBp := trBody_valid hp
  have hBp' := trBody_valid hp.shift
  have hnA : IsFormula SourceL (neg SourceL (tr (substs1 PA194PAeq.language t p))) :=
    IsSemiformula.neg_iff.mpr (tr_valid hA)
  have hexp : IsFormula SourceL (tr (^∃ p)) := tr_valid (IsSemiformula.exs.mpr (by simpa using hp))
  have hX : IsFormula SourceL (tr (^∃ (peq (^#(0 : V)) (termBShift PA194PAeq.language t)))) :=
    tr_valid (IsSemiformula.exs.mpr (by simpa using he))
  have hΔ : IsFormulaSet SourceL
      (insert (neg SourceL (tr (substs1 PA194PAeq.language t p))) (insert (tr (^∃ p)) (∅ : V))) :=
    fs_cons hnA (fs_cons hexp fs_nil)
  rw [singleton_eq_insert]
  refine GDerivable.cut (tr (^∃ (peq (^#(0 : V)) (termBShift PA194PAeq.language t))))
    (GDerivable.wk (fs_cons hX hΔ) (by set_tac) (F.totEq t ht)) ?_
  -- the negated totality formula is a relativized universal formula
  have e0 : neg SourceL (tr (^∃ (peq (^#(0 : V)) (termBShift PA194PAeq.language t)))) =
      ^∀ (guardBody ^⋎ neg SourceL (trBody (peq (^#(0 : V)) (termBShift PA194PAeq.language t)))) := by
    rw [tr_exs he, neg_ex_rel hBe]
  have e1 : free SourceL (neg SourceL (trBody (peq (^#(0 : V)) (termBShift PA194PAeq.language t)))) =
      neg SourceL (tr (peq (^&(0 : V)) (termShift PA194PAeq.language t))) := by
    rw [free_negS hBe, ← tr_free he, free_peq_bvar ht]
  have e2 : shift SourceL (neg SourceL (tr (substs1 PA194PAeq.language t p))) =
      neg SourceL (tr (substs1 PA194PAeq.language (termShift PA194PAeq.language t)
        (shift PA194PAeq.language p))) := by
    rw [shift_neg_tr hA, shift_substs1 hp ht]
  have e3 : shift SourceL (tr (^∃ p)) =
      ^∃ (domainCode (^#(0 : V)) ^⋏ trBody (shift PA194PAeq.language p)) := by
    rw [← tr_shift (IsSemiformula.exs.mpr (by simpa using hp)), shift_exs hp.isUFormula,
      tr_exs hp.shift]
  have e4 : substs1 SourceL (^&(0 : V)) (trBody (shift PA194PAeq.language p)) =
      tr (substs1 PA194PAeq.language (^&(0 : V)) (shift PA194PAeq.language p)) :=
    (tr_substs1_fvar hp.shift (0 : V)).symm
  have hL := leibniz F (0 : V) hp.shift ht.termShift
  unfold leibnizSeq at hL
  have hnX : IsFormula SourceL
      (^∀ (guardBody ^⋎ neg SourceL (trBody (peq (^#(0 : V)) (termBShift PA194PAeq.language t))))) := by
    rw [← e0]
    exact IsSemiformula.neg_iff.mpr hX
  rw [e0]
  refine GDerivable.all_rel (IsSemiformula.neg_iff.mpr hBe) (by simp) ?_
  rw [mem_setShift_insert, mem_setShift_insert, mem_setShift_insert, setShift_empty, e1, e2, e3]
  have hE' : IsFormula SourceL (neg SourceL (tr (peq (^&(0 : V))
      (termShift PA194PAeq.language t)))) :=
    IsSemiformula.neg_iff.mpr (tr_valid (peq_valid (by simp) ht.termShift))
  have hXt : IsFormula SourceL (tr (substs1 PA194PAeq.language (termShift PA194PAeq.language t)
      (shift PA194PAeq.language p))) := tr_valid (IsSemiformula.substs1 ht.termShift hp.shift)
  have hXc : IsFormula SourceL (tr (substs1 PA194PAeq.language (^&(0 : V))
      (shift PA194PAeq.language p))) := tr_valid (IsSemiformula.substs1 (by simp) hp.shift)
  have hex' : IsFormula SourceL
      (^∃ (domainCode (^#(0 : V)) ^⋏ trBody (shift PA194PAeq.language p))) := by
    simpa using IsSemiformula.and.mpr ⟨domainBody_valid (V := V),hBp'⟩
  refine GDerivable.ex_rel hBp' (by simp) (0 : V) ?_
  rw [e4]
  exact GDerivable.wk (fs_cons hXc (fs_cons hE' (fs_cons hnX.shift
    (fs_cons (IsSemiformula.neg_iff.mpr hXt) (fs_cons hex' fs_nil))))) (by set_tac) hL

variable (U : Theory PA194PAeq.language) [U.Δ₁]

/-- The interface of the compiler, with the existential rule supplied by the term facts. -/
theorem interpretation_of_termFacts (F : TermFacts (V := V) T)
    (hax : ∀ φ : V, IsSemiformula PA194PAeq.language 0 φ → φ ∈ U.Δ₁Class →
      GDerivable T ({tr φ} : V))
    (hdom : Provable T (^∃ (domainCode (^#(0 : V))))) : Interpretation (V := V) U T where
  axioms := hax
  witness := fun _ _ hp ht _ => witness_of_termFacts F hp ht
  inhabited := hdom

#print axioms free_subst_qVec
#print axioms leibniz
#print axioms witness_of_termFacts
#print axioms interpretation_of_termFacts
end generic
end PA194GuardedCompiler
