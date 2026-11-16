import PA194NameForms
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Code identities and two derivations for the translated induction axiom

* `trBody` commutes with disjunction, negation and shift.
* `leibnizAll`: from `tr (p[t])`, every name of `t` satisfies `p`; the universally closed form
  of the Leibniz lemma of `PA194Leibniz`.
* `indBody p`: the induction axiom of the arithmetic language for a formula `p` of arity one,
  before the closure of its parameters, and its translation.
* `tr_close_step`: a guarded derivation of `tr (free b)` gives one of `tr (∀ b)`.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### `trBody` and the connectives -/

theorem trBody_or {a b : V} (ha : IsSemiformula PA194PAeq.language 1 a)
    (hb : IsSemiformula PA194PAeq.language 1 b) : trBody (a ^⋎ b) = trBody a ^⋎ trBody b := by
  have hid := idParam_identity ((a ^⋎ b) + 1 : V)
  have h := translate_or (formulaChildParameters (idParam ((a ^⋎ b) + 1))) a b ha.isUFormula
    hb.isUFormula
  rw [trBody_eq hid ha (by simpa using lt_trans (lt_qqOr_left a b) (lt_add_one _)),
    trBody_eq hid hb (by simpa using lt_trans (lt_qqOr_right a b) (lt_add_one _))] at h
  exact h

theorem trBody_neg {p : V} (hp : IsSemiformula PA194PAeq.language 1 p) :
    trBody (neg PA194PAeq.language p) = neg SourceL (trBody p) := by
  have hid := idParam_identity (p + neg PA194PAeq.language p + 1 : V)
  have hchild : ParametersValid 1 1
      (formulaChildParameters (idParam (p + neg PA194PAeq.language p + 1))) := by
    simpa using formulaChildParameters_valid hid.1
  have h1 : p < len (nth (idParam (p + neg PA194PAeq.language p + 1)) 1) := by
    simpa using lt_succ_of_le' (le_self_add (a := p) (b := neg PA194PAeq.language p))
  have h2 : neg PA194PAeq.language p <
      len (nth (idParam (p + neg PA194PAeq.language p + 1)) 1) := by
    simpa using lt_succ_of_le' (le_add_self (a := neg PA194PAeq.language p) (b := p))
  have h := translateFormula_neg hp.isUFormula 1 1 _ hp hchild
    (by rw [hid.child_free_len]; exact h1) (by rw [hid.child_free_len]; exact h2)
  rw [trBody_eq hid hp h1, trBody_eq hid (IsSemiformula.neg_iff.mpr hp) h2] at h
  exact h

theorem trBody_shift {p : V} (hp : IsSemiformula PA194PAeq.language 1 p) :
    trBody (shift PA194PAeq.language p) = shift SourceL (trBody p) := by
  have hid := idParam_identity (p + shift PA194PAeq.language p + 1 : V)
  have h1 : p < len (nth (idParam (p + shift PA194PAeq.language p + 1)) 1) := by
    simpa using lt_succ_of_le' (le_self_add (a := p) (b := shift PA194PAeq.language p))
  have h2 : shift PA194PAeq.language p <
      len (nth (idParam (p + shift PA194PAeq.language p + 1)) 1) := by
    simpa using lt_succ_of_le' (le_add_self (a := shift PA194PAeq.language p) (b := p))
  have hchild : ParametersValid 1 1
      (formulaChildParameters (idParam (p + shift PA194PAeq.language p + 1))) := by
    simpa using formulaChildParameters_valid hid.1
  have hrelS : EnvShiftRel 1 (formulaChildParameters (idParam (p + shift PA194PAeq.language p + 1)))
      (formulaChildParameters (idParam (p + shift PA194PAeq.language p + 1))) := by
    simpa using hid.envShiftRel.formulaChild hid.1 hid.1
  have hA := formula_shift hp.isUFormula 1 1 _ _ hp hchild hchild hrelS
    (by rw [hid.child_free_len]; exact h1) (by rw [hid.child_free_len]; exact h2)
  rw [trBody_eq hid hp.shift h2, trBody_eq hid hp h1] at hA
  exact hA

theorem free_orS {X Y : V} (hX : IsSemiformula SourceL 1 X) (hY : IsSemiformula SourceL 1 Y) :
    free SourceL (X ^⋎ Y) = free SourceL X ^⋎ free SourceL Y := by
  show subst SourceL (?[^&(0 : V)] : V) (shift SourceL (X ^⋎ Y)) =
    subst SourceL (?[^&(0 : V)] : V) (shift SourceL X) ^⋎
      subst SourceL (?[^&(0 : V)] : V) (shift SourceL Y)
  rw [shift_or hX.isUFormula hY.isUFormula, substs_or hX.shift.isUFormula hY.shift.isUFormula]

/-! ### The universally closed Leibniz lemma -/

/-- Every name of `t` satisfies `p`. -/
noncomputable def allNames (t p : V) : V :=
  ^∀ (neg PA194PAeq.language (peq (^#(0 : V)) (termBShift PA194PAeq.language t)) ^⋎ p)

theorem allNames_body_valid {t p : V} (ht : IsSemiterm PA194PAeq.language 0 t)
    (hp : IsSemiformula PA194PAeq.language 1 p) :
    IsSemiformula PA194PAeq.language 1
      (neg PA194PAeq.language (peq (^#(0 : V)) (termBShift PA194PAeq.language t)) ^⋎ p) :=
  IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr (peq_valid (by simp) (bShift_valid ht)), hp⟩
theorem allNames_valid {t p : V} (ht : IsSemiterm PA194PAeq.language 0 t)
    (hp : IsSemiformula PA194PAeq.language 1 p) :
    IsSemiformula PA194PAeq.language 0 (allNames t p) := by
  unfold allNames
  exact IsSemiformula.all.mpr (by simpa using allNames_body_valid ht hp)

/-- The translation of `allNames t p`, with the value formula of `t` as the only part that
depends on `t`. -/
theorem tr_allNames {t p : V} (ht : IsSemiterm PA194PAeq.language 0 t)
    (hp : IsSemiformula PA194PAeq.language 1 p) :
    tr (allNames t p) = ^∀ (guardBody ^⋎
      (neg SourceL (eqForm (variableValue (^#(1 : V)) (^#(2 : V)))
          (substs1 SourceL (^#(0 : V)) (valBody t))) ^⋎ trBody p)) := by
  have h0 : IsSemiterm PA194PAeq.language 1 (^#(0 : V)) := by simp
  have ht1 : IsSemiterm PA194PAeq.language 1 t := by
    simpa [termBShift_closed t ht] using bShift_valid ht
  have he : IsSemiformula PA194PAeq.language 1 (peq (^#(0 : V)) t) := peq_valid h0 ht1
  have hne : IsSemiformula PA194PAeq.language 1 (neg PA194PAeq.language (peq (^#(0 : V)) t)) :=
    IsSemiformula.neg_iff.mpr he
  have hb : IsSemiformula PA194PAeq.language 1
      (neg PA194PAeq.language (peq (^#(0 : V)) t) ^⋎ p) := IsSemiformula.or.mpr ⟨hne,hp⟩
  have l1 : t < peq (^#(0 : V)) t + 1 := lt_trans (lt_peq_right _ _) (lt_add_one _)
  have ea : trBody (peq (^#(0 : V)) t) =
      eqForm (variableValue (^#(1 : V)) (^#(2 : V))) (substs1 SourceL (^#(0 : V)) (valBody t)) :=
    atom_one ht l1
  unfold allNames
  rw [termBShift_closed t ht, tr_all hb, trBody_or hne hp, trBody_neg he, ea]

theorem leibnizAll {T : Theory SourceL} [T.Δ₁] (F : TermFacts (V := V) T) {p t : V}
    (hp : IsSemiformula PA194PAeq.language 1 p) (ht : IsSemiterm PA194PAeq.language 0 t) :
    GDerivable T (insert (neg SourceL (tr (substs1 PA194PAeq.language t p)))
      (insert (tr (allNames t p)) (∅ : V))) := by
  have h0 : IsSemiterm PA194PAeq.language 1 (^#(0 : V)) := by simp
  have he : IsSemiformula PA194PAeq.language 1
      (peq (^#(0 : V)) (termBShift PA194PAeq.language t)) := peq_valid h0 (bShift_valid ht)
  have hne := IsSemiformula.neg_iff.mpr he
  have hb := allNames_body_valid ht hp
  have hBe := trBody_valid he
  have hBp := trBody_valid hp
  have hBb := trBody_valid hb
  have hA : IsSemiformula PA194PAeq.language 0 (substs1 PA194PAeq.language t p) :=
    IsSemiformula.substs1 ht hp
  have hall := allNames_valid ht hp
  have etr : tr (allNames t p) = ^∀ (guardBody ^⋎ trBody
      (neg PA194PAeq.language (peq (^#(0 : V)) (termBShift PA194PAeq.language t)) ^⋎ p)) :=
    tr_all hb
  have efree : free PA194PAeq.language p =
      substs1 PA194PAeq.language (^&(0 : V)) (shift PA194PAeq.language p) := rfl
  have e1 : free SourceL (trBody
      (neg PA194PAeq.language (peq (^#(0 : V)) (termBShift PA194PAeq.language t)) ^⋎ p)) =
      neg SourceL (tr (peq (^&(0 : V)) (termShift PA194PAeq.language t))) ^⋎
        tr (substs1 PA194PAeq.language (^&(0 : V)) (shift PA194PAeq.language p)) := by
    rw [trBody_or hne hp, trBody_neg he, free_orS (IsSemiformula.neg_iff.mpr hBe) hBp,
      free_negS hBe, ← tr_free he, free_peq_bvar ht, ← tr_free hp, efree]
  have e2 : shift SourceL (neg SourceL (tr (substs1 PA194PAeq.language t p))) =
      neg SourceL (tr (substs1 PA194PAeq.language (termShift PA194PAeq.language t)
        (shift PA194PAeq.language p))) := by
    rw [shift_neg_tr hA, shift_substs1 hp ht]
  have hL := leibniz F (0 : V) hp.shift ht.termShift
  unfold leibnizSeq at hL
  have hE' : IsFormula SourceL (neg SourceL (tr (peq (^&(0 : V))
      (termShift PA194PAeq.language t)))) :=
    IsSemiformula.neg_iff.mpr (tr_valid (peq_valid (by simp) ht.termShift))
  have hXt : IsFormula SourceL (neg SourceL (tr (substs1 PA194PAeq.language
      (termShift PA194PAeq.language t) (shift PA194PAeq.language p)))) :=
    IsSemiformula.neg_iff.mpr (tr_valid (IsSemiformula.substs1 ht.termShift hp.shift))
  have hXc : IsFormula SourceL (tr (substs1 PA194PAeq.language (^&(0 : V))
      (shift PA194PAeq.language p))) := tr_valid (IsSemiformula.substs1 (by simp) hp.shift)
  have hAllF : IsFormula SourceL (tr (allNames t p)) := tr_valid hall
  rw [etr] at hAllF ⊢
  refine GDerivable.all_rel hBb (by simp) ?_
  rw [mem_setShift_insert, mem_setShift_insert, setShift_empty, e1, e2]
  have hor : IsFormula SourceL (neg SourceL (tr (peq (^&(0 : V))
      (termShift PA194PAeq.language t))) ^⋎
        tr (substs1 PA194PAeq.language (^&(0 : V)) (shift PA194PAeq.language p))) :=
    IsSemiformula.or.mpr ⟨hE',hXc⟩
  refine GDerivable.or_m (p := neg SourceL (tr (peq (^&(0 : V))
      (termShift PA194PAeq.language t))))
    (q := tr (substs1 PA194PAeq.language (^&(0 : V)) (shift PA194PAeq.language p)))
    (by simp) ?_
  exact GDerivable.wk (fs_cons hE' (fs_cons hXc (fs_cons hor (fs_cons hXt
    (fs_cons hAllF.shift fs_nil))))) (by set_tac) hL

/-! ### The induction axiom before the closure of its parameters -/

/-- The term `S(#0)`. -/
noncomputable def succVar : V := ^func (1 : V) 1 (?[^#(0 : V)] : V)
theorem succVar_valid : IsSemiterm PA194PAeq.language 1 (succVar : V) := by
  unfold succVar
  simp

/-- `p[0] → (∀x (p → p[S x]) → ∀x p)`. -/
noncomputable def indBody (p : V) : V :=
  imp PA194PAeq.language (substs1 PA194PAeq.language zeroT p)
    (imp PA194PAeq.language
      (^∀ (imp PA194PAeq.language p (substs1 PA194PAeq.language succVar p))) (^∀ p))

theorem substs1_succVar_valid {p : V} (hp : IsSemiformula PA194PAeq.language 1 p) :
    IsSemiformula PA194PAeq.language 1 (substs1 PA194PAeq.language succVar p) := by
  have hw : IsSemitermVec PA194PAeq.language 1 1 (?[succVar] : V) := by simp [succVar_valid]
  exact hp.subst hw

/-- Opening the bound variable of `p[S x]` gives `(shift p)[S(&0)]`. -/
theorem free_substs1_succVar {p : V} (hp : IsSemiformula PA194PAeq.language 1 p) :
    free PA194PAeq.language (substs1 PA194PAeq.language succVar p) =
      substs1 PA194PAeq.language (succT (^&(0 : V))) (shift PA194PAeq.language p) := by
  have hw : IsSemitermVec PA194PAeq.language 1 1 (?[succVar] : V) := by simp [succVar_valid]
  have hv : IsSemitermVec PA194PAeq.language 1 0 (?[^&(0 : V)] : V) := by simp
  show subst PA194PAeq.language (?[^&(0 : V)] : V)
      (shift PA194PAeq.language (subst PA194PAeq.language (?[succVar] : V) p)) =
    subst PA194PAeq.language (?[succT (^&(0 : V))] : V) (shift PA194PAeq.language p)
  rw [shift_substs hp hw]
  have e1 : termShiftVec PA194PAeq.language 1 (?[succVar] : V) = (?[succVar] : V) := by
    rw [termShiftVec_cons₁ succVar_valid.isUTerm]
    unfold succVar
    simp
  rw [e1, substs_substs hp.shift hv hw]
  have e2 : termSubstVec PA194PAeq.language 1 (?[^&(0 : V)] : V) (?[succVar] : V) =
      (?[succT (^&(0 : V))] : V) := by
    rw [termSubstVec_cons₁ succVar_valid.isUTerm]
    unfold succVar succT
    simp
  rw [e2]

theorem tr_indBody {p : V} (hp : IsSemiformula PA194PAeq.language 1 p) :
    tr (indBody p) = neg SourceL (tr (substs1 PA194PAeq.language zeroT p)) ^⋎
      (neg SourceL (^∀ (guardBody ^⋎ (neg SourceL (trBody p) ^⋎
          trBody (substs1 PA194PAeq.language succVar p)))) ^⋎
        ^∀ (guardBody ^⋎ trBody p)) := by
  have hpS := substs1_succVar_valid hp
  have hp0 : IsSemiformula PA194PAeq.language 0 (substs1 PA194PAeq.language zeroT p) :=
    IsSemiformula.substs1 zeroT_valid hp
  have himp : IsSemiformula PA194PAeq.language 1
      (neg PA194PAeq.language p ^⋎ substs1 PA194PAeq.language succVar p) :=
    IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr hp,hpS⟩
  have hall1 : IsSemiformula PA194PAeq.language 0
      (^∀ (neg PA194PAeq.language p ^⋎ substs1 PA194PAeq.language succVar p)) :=
    IsSemiformula.all.mpr (by simpa using himp)
  have hall2 : IsSemiformula PA194PAeq.language 0 (^∀ p) :=
    IsSemiformula.all.mpr (by simpa using hp)
  have hinner : IsSemiformula PA194PAeq.language 0
      (neg PA194PAeq.language (^∀ (neg PA194PAeq.language p ^⋎
        substs1 PA194PAeq.language succVar p)) ^⋎ ^∀ p) :=
    IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr hall1,hall2⟩
  show tr (neg PA194PAeq.language (substs1 PA194PAeq.language zeroT p) ^⋎
      (neg PA194PAeq.language (^∀ (neg PA194PAeq.language p ^⋎
        substs1 PA194PAeq.language succVar p)) ^⋎ ^∀ p)) = _
  rw [tr_or (IsSemiformula.neg_iff.mpr hp0) hinner, tr_neg hp0,
    tr_or (IsSemiformula.neg_iff.mpr hall1) hall2, tr_neg hall1, tr_all himp, tr_all hp,
    trBody_or (IsSemiformula.neg_iff.mpr hp) hpS, trBody_neg hp]

/-! ### One step of the closure of parameters -/

theorem tr_close_step {T : Theory SourceL} [T.Δ₁] {b : V}
    (hb : IsSemiformula PA194PAeq.language 1 b)
    (h : GDerivable T (insert (tr (free PA194PAeq.language b)) (∅ : V))) :
    GDerivable T (insert (tr (^∀ b)) (∅ : V)) := by
  have hall : IsFormula SourceL (tr (^∀ b)) := tr_valid (IsSemiformula.all.mpr (by simpa using hb))
  have hf : IsFormula SourceL (tr (free PA194PAeq.language b)) := tr_valid hb.free
  rw [tr_all hb] at hall ⊢
  refine GDerivable.all_rel (trBody_valid hb) (by simp) ?_
  rw [mem_setShift_insert, setShift_empty, ← tr_free hb]
  exact GDerivable.wk (fs_cons hf (fs_cons hall.shift fs_nil)) (by set_tac) h

#print axioms trBody_or
#print axioms trBody_neg
#print axioms tr_allNames
#print axioms leibnizAll
#print axioms free_substs1_succVar
#print axioms tr_indBody
#print axioms tr_close_step
end generic
end PA194GuardedCompiler
