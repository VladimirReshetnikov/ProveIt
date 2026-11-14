import PA194BindAllTerm
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194BindAllFormula
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindAllTerm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y depth k R v. ∃ w, !(PA194BindAllTerm.blueprint.resultVec ℒₒᵣ) w k v depth ∧ !qqRelDef y k R w”
  nrel := .mkSigma “y depth k R v. ∃ w, !(PA194BindAllTerm.blueprint.resultVec ℒₒᵣ) w k v depth ∧ !qqNRelDef y k R w”
  verum := .mkSigma “y depth. !qqVerumDef y”
  falsum := .mkSigma “y depth. !qqFalsumDef y”
  and := .mkSigma “y depth p q u v. !qqAndDef y u v”
  or := .mkSigma “y depth p q u v. !qqOrDef y u v”
  all := .mkSigma “y depth p u. !qqAllDef y u”
  exs := .mkSigma “y depth p u. !qqExsDef y u”
  allChanges := .mkSigma “next depth. next = depth+1”
  exsChanges := .mkSigma “next depth. next = depth+1”
noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel d k R v := ^rel k R (PA194BindAllTerm.construction.resultVec ℒₒᵣ ![d] k v)
  nrel d k R v := ^nrel k R (PA194BindAllTerm.construction.resultVec ℒₒᵣ ![d] k v)
  verum _ := ^⊤
  falsum _ := ^⊥
  and _ _ _ u v := u ^⋏ v
  or _ _ _ u v := u ^⋎ v
  all _ _ u := ^∀ u
  exs _ _ u := ^∃ u
  allChanges d := d+1
  exsChanges d := d+1
  rel_defined := .mk fun v => by simp [blueprint,PA194BindAllTerm.construction.eval_resultVec,Matrix.comp_vecCons',Matrix.constant_eq_singleton]
  nrel_defined := .mk fun v => by simp [blueprint,PA194BindAllTerm.construction.eval_resultVec,Matrix.comp_vecCons',Matrix.constant_eq_singleton]
  verum_defined := .mk fun v => by simp [blueprint]
  falsum_defined := .mk fun v => by simp [blueprint]
  and_defined := .mk fun v => by simp [blueprint]
  or_defined := .mk fun v => by simp [blueprint]
  all_defined := .mk fun v => by simp [blueprint]
  exs_defined := .mk fun v => by simp [blueprint]
  allChanges_defined := .mk fun v => by simp [blueprint]
  exChanges_defined := .mk fun v => by simp [blueprint]
noncomputable def bindAll (d p : V) : V := construction.result ℒₒᵣ d p
instance bindAll_definable : 𝚺₁-Function₂ (bindAll (V := V)) := construction.result_defined.to_definable
lemma bindAll_rel (d k r v : V) (hr : (ℒₒᵣ : Language).IsRel k r) (hv : IsUTermVec ℒₒᵣ k v) :
  bindAll d (^rel k r v) = ^rel k r (bindAllVec d k v) := by simp [bindAll,bindAllVec,construction,hr,hv]
lemma bindAll_nrel (d k r v : V) (hr : (ℒₒᵣ : Language).IsRel k r) (hv : IsUTermVec ℒₒᵣ k v) :
  bindAll d (^nrel k r v) = ^nrel k r (bindAllVec d k v) := by simp [bindAll,bindAllVec,construction,hr,hv]
@[simp] lemma bindAll_verum (d : V) : bindAll d ^⊤ = ^⊤ := by simp [bindAll,construction]
@[simp] lemma bindAll_falsum (d : V) : bindAll d ^⊥ = ^⊥ := by simp [bindAll,construction]
lemma bindAll_and (d p q : V) (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
  bindAll d (p ^⋏ q) = bindAll d p ^⋏ bindAll d q := by simp [bindAll,construction,hp,hq]
lemma bindAll_or (d p q : V) (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
  bindAll d (p ^⋎ q) = bindAll d p ^⋎ bindAll d q := by simp [bindAll,construction,hp,hq]
lemma bindAll_all (d p : V) (hp : IsUFormula ℒₒᵣ p) :
  bindAll d (^∀ p) = ^∀ (bindAll (d+1) p) := by simp [bindAll,construction,hp]
lemma bindAll_exs (d p : V) (hp : IsUFormula ℒₒᵣ p) :
  bindAll d (^∃ p) = ^∃ (bindAll (d+1) p) := by simp [bindAll,construction,hp]
lemma bindAllVec_shift_fixed (d k v : V) (hv : IsUTermVec ℒₒᵣ k v) :
    termShiftVec ℒₒᵣ k (bindAllVec d k v) = bindAllVec d k v := by
  have hvec := bindAllVec_isUTerm d k v hv
  apply nth_ext' k
  · simp [hvec]
  · simp [bindAllVec, hv]
  · intro i hi
    rw [nth_termShiftVec hvec hi]
    rw [show (bindAllVec d k v).[i] = PA194BindAllTerm.bindAll d v.[i] by
      exact Language.TermRec.Construction.nth_resultVec _ _ _ hv hi]
    exact bindAll_shift_fixed d _ (hv.nth hi)

theorem bindAll_wf_fixed (d p : V) (hp : IsSemiformula ℒₒᵣ d p) :
    IsUFormula ℒₒᵣ (bindAll d p) ∧ shift ℒₒᵣ (bindAll d p) = bindAll d p := by
  have hdef : 𝚺₁-Relation (fun d p : V => IsUFormula ℒₒᵣ (bindAll d p) ∧ shift ℒₒᵣ (bindAll d p) = bindAll d p) := by definability
  apply IsSemiformula.sigma1_structural_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro n k r v hr hv
    rw [bindAll_rel n k r v hr hv.isUTerm]
    have hw := bindAllVec_isUTerm n k v hv.isUTerm
    constructor
    · simp [hr,hw]
    · rw [shift_rel hr hw,bindAllVec_shift_fixed n k v hv.isUTerm]
  · intro n k r v hr hv
    rw [bindAll_nrel n k r v hr hv.isUTerm]
    have hw := bindAllVec_isUTerm n k v hv.isUTerm
    constructor
    · simp [hr,hw]
    · rw [shift_nrel hr hw,bindAllVec_shift_fixed n k v hv.isUTerm]
  · intro n; simp
  · intro n; simp
  · intro n p q hp hq ihp ihq
    rw [bindAll_and n p q hp.isUFormula hq.isUFormula]
    constructor
    · simp [ihp.1,ihq.1]
    · rw [shift_and ihp.1 ihq.1,ihp.2,ihq.2]
  · intro n p q hp hq ihp ihq
    rw [bindAll_or n p q hp.isUFormula hq.isUFormula]
    constructor
    · simp [ihp.1,ihq.1]
    · rw [shift_or ihp.1 ihq.1,ihp.2,ihq.2]
  · intro n p hp ih
    rw [bindAll_all n p hp.isUFormula]
    constructor
    · simp [ih.1]
    · rw [shift_all ih.1,ih.2]
  · intro n p hp ih
    rw [bindAll_exs n p hp.isUFormula]
    constructor
    · simp [ih.1]
    · rw [shift_exs ih.1,ih.2]
#print axioms bindAll_wf_fixed
#print axioms construction
#print axioms bindAll_all
end PA194BindAllFormula
