import PA194GuardedUniversalIntro
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem uniqueVariableBody_shift (i : V) :
    shift PA194PAeq.language (uniqueVariableBody i) = uniqueVariableBody (i+1) := by
  have h1 : IsSemiformula PA194PAeq.language 2 (peq (^#(1 : V)) (^&i)) := peq_valid (by simp) (by simp)
  have h0 : IsSemiformula PA194PAeq.language 2 (peq (^#(0 : V)) (^&i)) := peq_valid (by simp) (by simp)
  have h2 : IsSemiformula PA194PAeq.language 2 (peq (^#(1 : V)) (^#(0 : V))) := peq_valid (by simp) (by simp)
  unfold uniqueVariableBody
  rw [shift_or (IsSemiformula.neg_iff.mpr h1).isUFormula
    (IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr h0,h2⟩).isUFormula,
    shift_or (IsSemiformula.neg_iff.mpr h0).isUFormula h2.isUFormula,
    shift_neg h1, shift_neg h0]
  rw [shift_peq (show IsSemiterm PA194PAeq.language 2 (^#(1 : V)) by simp)
     (show IsSemiterm PA194PAeq.language 2 (^&i) by simp),
    shift_peq (show IsSemiterm PA194PAeq.language 2 (^#(0 : V)) by simp)
     (show IsSemiterm PA194PAeq.language 2 (^&i) by simp),
    shift_peq (show IsSemiterm PA194PAeq.language 2 (^#(1 : V)) by simp)
     (show IsSemiterm PA194PAeq.language 2 (^#(0 : V)) by simp)]
  simp

theorem subst_peq_general {w n a b : V} (ha : IsSemiterm PA194PAeq.language n a)
    (hb : IsSemiterm PA194PAeq.language n b) :
    subst PA194PAeq.language w (peq a b) =
      peq (termSubst PA194PAeq.language w a) (termSubst PA194PAeq.language w b) := by
  have hv : IsUTermVec PA194PAeq.language 2 (?[a,b] : V) := by simp [ha.isUTerm,hb.isUTerm]
  unfold peq
  rw [substs_rel isRel_eq hv,termSubstVec_cons₂ ha.isUTerm hb.isUTerm]

theorem openedUniqueVariableBody (i : V) :
    openedDoubleBody (uniqueVariableBody i) =
      neg PA194PAeq.language (peq (^&(0 : V)) (^&(i+1))) ^⋎
      (neg PA194PAeq.language (peq (^#(0 : V)) (^&(i+1))) ^⋎ peq (^&(0 : V)) (^#(0 : V))) := by
  unfold openedDoubleBody
  rw [uniqueVariableBody_shift i, qVecA_singleton (show IsSemiterm PA194PAeq.language 0 (^&(0 : V)) by simp), termBShift_fvar]
  have h1 : IsSemiformula PA194PAeq.language 2 (peq (^#(1 : V)) (^&(i+1))) := peq_valid (by simp) (by simp)
  have h0 : IsSemiformula PA194PAeq.language 2 (peq (^#(0 : V)) (^&(i+1))) := peq_valid (by simp) (by simp)
  have h2 : IsSemiformula PA194PAeq.language 2 (peq (^#(1 : V)) (^#(0 : V))) := peq_valid (by simp) (by simp)
  have hw : IsSemitermVec PA194PAeq.language 2 1 (?[ ^#(0 : V), ^&(0 : V)] : V) := by simp
  unfold uniqueVariableBody
  rw [substs_or (IsSemiformula.neg_iff.mpr h1).isUFormula
    (IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr h0,h2⟩).isUFormula,
    substs_or (IsSemiformula.neg_iff.mpr h0).isUFormula h2.isUFormula,
    substs_neg h1 hw,substs_neg h0 hw,
    subst_peq_general (show IsSemiterm PA194PAeq.language 2 (^#(1 : V)) by simp)
      (show IsSemiterm PA194PAeq.language 2 (^&(i+1)) by simp),
    subst_peq_general (show IsSemiterm PA194PAeq.language 2 (^#(0 : V)) by simp)
      (show IsSemiterm PA194PAeq.language 2 (^&(i+1)) by simp),
    subst_peq_general (show IsSemiterm PA194PAeq.language 2 (^#(1 : V)) by simp)
      (show IsSemiterm PA194PAeq.language 2 (^#(0 : V)) by simp)]
  simp [termSubst_bvar,termSubst_fvar]

theorem uniqueVariable_opened_exact (i : V) :
    free PA194PAeq.language (openedDoubleBody (uniqueVariableBody i)) =
      neg PA194PAeq.language (peq (^&(1 : V)) (^&(i+2))) ^⋎
        (neg PA194PAeq.language (peq (^&(0 : V)) (^&(i+2))) ^⋎ peq (^&(1 : V)) (^&(0 : V))) := by
  rw [openedUniqueVariableBody]
  have h1 : IsSemiformula PA194PAeq.language 1 (peq (^&(0 : V)) (^&(i+1))) := peq_valid (by simp) (by simp)
  have h0 : IsSemiformula PA194PAeq.language 1 (peq (^#(0 : V)) (^&(i+1))) := peq_valid (by simp) (by simp)
  have h2 : IsSemiformula PA194PAeq.language 1 (peq (^&(0 : V)) (^#(0 : V))) := peq_valid (by simp) (by simp)
  show substs1 PA194PAeq.language (^&(0 : V))
    (shift PA194PAeq.language (neg PA194PAeq.language (peq (^&(0 : V)) (^&(i+1))) ^⋎
      (neg PA194PAeq.language (peq (^#(0 : V)) (^&(i+1))) ^⋎ peq (^&(0 : V)) (^#(0 : V))))) = _
  rw [shift_or (IsSemiformula.neg_iff.mpr h1).isUFormula
    (IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr h0,h2⟩).isUFormula,
    shift_or (IsSemiformula.neg_iff.mpr h0).isUFormula h2.isUFormula,
    shift_neg h1,shift_neg h0,
    shift_peq (show IsSemiterm PA194PAeq.language 1 (^&(0 : V)) by simp)
      (show IsSemiterm PA194PAeq.language 1 (^&(i+1)) by simp),
    shift_peq (show IsSemiterm PA194PAeq.language 1 (^#(0 : V)) by simp)
      (show IsSemiterm PA194PAeq.language 1 (^&(i+1)) by simp),
    shift_peq (show IsSemiterm PA194PAeq.language 1 (^&(0 : V)) by simp)
      (show IsSemiterm PA194PAeq.language 1 (^#(0 : V)) by simp)]
  simp only [termShift_fvar,termShift_bvar]
  have h1' : IsSemiformula PA194PAeq.language 1 (peq (^&(0+1 : V)) (^&(i+1+1))) := peq_valid (by simp) (by simp)
  have h0' : IsSemiformula PA194PAeq.language 1 (peq (^#(0 : V)) (^&(i+1+1))) := peq_valid (by simp) (by simp)
  have h2' : IsSemiformula PA194PAeq.language 1 (peq (^&(0+1 : V)) (^#(0 : V))) := peq_valid (by simp) (by simp)
  rw [substs1_orA (IsSemiformula.neg_iff.mpr h1')
    (IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr h0',h2'⟩),
    substs1_orA (IsSemiformula.neg_iff.mpr h0') h2',
    substs1_negA h1' (by simp),substs1_negA h0' (by simp)]
  rw [substs1_peq (by simp) (by simp),substs1_peq (by simp) (by simp),substs1_peq (by simp) (by simp)]
  simp [termSubst_fvar,termSubst_bvar,add_assoc,one_add_one_eq_two]

/-- Pack a three-formula guarded sequent into its nested disjunction. -/
theorem guarded_or3 {T : Theory SourceL} [T.Δ₁] {a b c : V}
    (ha : IsFormula SourceL a) (hb : IsFormula SourceL b) (hc : IsFormula SourceL c)
    (h : GDerivable T (insert a (insert b ({c} : V)))) :
    GDerivable T ({a ^⋎ (b ^⋎ c)} : V) := by
  let q : V := a ^⋎ (b ^⋎ c)
  let r : V := b ^⋎ c
  have hr : IsFormula SourceL r := IsSemiformula.or.mpr ⟨hb,hc⟩
  have hq : IsFormula SourceL q := IsSemiformula.or.mpr ⟨ha,hr⟩
  have hs : IsFormulaSet SourceL ({q} : V) := by rw [singleton_eq_insert]; exact fs_cons hq fs_nil
  have hb' : GDerivable T (insert b (insert c (insert a (insert r ({q} : V))))) := by
    apply GDerivable.wk (fs_cons hb (fs_cons hc (fs_cons ha (fs_cons hr hs)))) _ h
    set_tac
  have hm : GDerivable T (insert a (insert r ({q} : V))) :=
    GDerivable.or_m (by simp [r]) hb'
  have hp : GDerivable T (insert a (insert r ({q} : V))) := hm
  exact GDerivable.or_m (p := a) (q := r) (by simp [q, r]) hp

/-- Uniqueness of variable names follows from pointwise equality cancellation. -/
theorem guarded_uVar_of_equality_cancellation {T : Theory SourceL} [T.Δ₁]
    (h : ∀ x y z : V, GDerivable T
      (insert (neg SourceL (tr (peq (^&x) (^&z))))
        (insert (neg SourceL (tr (peq (^&y) (^&z)))) ({tr (peq (^&x) (^&y))} : V)))) :
    ∀ i : V, GDerivable T ({tr (uniq (^&i))} : V) := by
  apply guarded_uVar_of_open
  intro i
  rw [uniqueVariable_opened_exact]
  let a : V := peq (^&(1 : V)) (^&(i+2))
  let b : V := peq (^&(0 : V)) (^&(i+2))
  let c : V := peq (^&(1 : V)) (^&(0 : V))
  have ha : IsSemiformula PA194PAeq.language 0 a := peq_valid (by simp) (by simp)
  have hb : IsSemiformula PA194PAeq.language 0 b := peq_valid (by simp) (by simp)
  have hc : IsSemiformula PA194PAeq.language 0 c := peq_valid (by simp) (by simp)
  change GDerivable T ({tr (neg PA194PAeq.language a ^⋎ (neg PA194PAeq.language b ^⋎ c))} : V)
  rw [tr_or (IsSemiformula.neg_iff.mpr ha) (IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr hb,hc⟩),
    tr_or (IsSemiformula.neg_iff.mpr hb) hc,tr_neg ha,tr_neg hb]
  apply guarded_or3 (IsSemiformula.neg_iff.mpr (tr_valid ha))
    (IsSemiformula.neg_iff.mpr (tr_valid hb)) (tr_valid hc)
  exact h 1 0 (i+2)

#print axioms guarded_uVar_of_equality_cancellation
#print axioms guarded_or3
#print axioms uniqueVariableBody_shift
#print axioms subst_peq_general
#print axioms openedUniqueVariableBody
#print axioms uniqueVariable_opened_exact
end generic
end PA194GuardedCompiler
