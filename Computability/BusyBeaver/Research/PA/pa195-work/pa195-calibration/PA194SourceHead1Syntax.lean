import PA194SourceHead5Preservation
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace PA194SourceHead1Syntax
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194GenericRenameBase PA194GenericRenameAxiom PA194GenericRenameRules PA194RenameShiftCompatibility PA194ReplacementOpening
open PA194SourceOutputWF PA194SourceRho8Preservation PA194SourceEqualityPreservation PA194SourceHead6Preservation PA194SourceHead5Preservation
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma term_identity (label depth t : M) (ht : IsSemiterm ℒₒᵣ depth t) :
    renameTerm replaceGraph replaceMap replaceGraph_correct (pair label label) t = t := by
  haveI := term_definable replaceGraph replaceMap replaceGraph_correct (pair label label)
  have hdef : 𝚺₁-Predicate (fun t : M => renameTerm replaceGraph replaceMap replaceGraph_correct (pair label label) t = t) := by definability
  apply IsSemiterm.sigma1_induction hdef (n := depth) ?_ ?_ ?_ t ht
  · intro z hz; simp [rename_bvar]
  · intro x; simp [rename_fvar,replaceMap]
  · intro k g v hg hv ih
    rw [rename_func replaceGraph replaceMap replaceGraph_correct (pair label label) k g v hg hv.isUTerm]
    congr 1
    apply nth_ext' k (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm) (by simpa using hv.lh)
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    exact ih i hi

lemma formula_identity (label depth φ : M) (hφ : IsSemiformula ℒₒᵣ depth φ) :
    renameFormula replaceGraph replaceMap replaceGraph_correct (pair label label) φ = φ := by
  haveI := formula_definable replaceGraph replaceMap replaceGraph_correct (pair label label)
  have hdef : 𝚺₁-Relation (fun n φ : M => renameFormula replaceGraph replaceMap replaceGraph_correct (pair label label) φ = φ) := by definability
  apply IsSemiformula.sigma1_structural_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hφ
  · intro n k r v hr hv
    rw [rename_rel replaceGraph replaceMap replaceGraph_correct (pair label label) k r v hr hv.isUTerm]
    congr 1
    apply nth_ext' k (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm) (by simpa using hv.lh)
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    exact term_identity label n v.[i] (hv.nth hi)
  · intro n k r v hr hv
    rw [rename_nrel replaceGraph replaceMap replaceGraph_correct (pair label label) k r v hr hv.isUTerm]
    congr 1
    apply nth_ext' k (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm) (by simpa using hv.lh)
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    exact term_identity label n v.[i] (hv.nth hi)
  · intro n; simp [rename_verum]
  · intro n; simp [rename_falsum]
  · intro n p q hp hq ihp ihq; simp [rename_and, hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p q hp hq ihp ihq; simp [rename_or, hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p hp ih; simp [rename_all, hp.isUFormula, ih]
  · intro n p hp ih; simp [rename_exs, hp.isUFormula, ih]

lemma reopen_identity (label φ : M) (hφ : IsFormula ℒₒᵣ φ) :
    substs1 ℒₒᵣ (^&label) (PA194InternalFormulaClose.close label 0 φ) = φ := by
  rw [← specialization_agreement label label φ hφ]
  exact formula_identity label 0 φ hφ
lemma close_term_twice (label depth t : M) (ht : IsSemiterm ℒₒᵣ depth t) :
    PA194InternalClose.close label (depth+1) (PA194InternalClose.close label depth t) = PA194InternalClose.close label depth t := by
  haveI := PA194InternalClose.close_definable label depth
  haveI := PA194InternalClose.close_definable label (depth+1)
  have hdef : 𝚺₁-Predicate (fun t : M => PA194InternalClose.close label (depth+1) (PA194InternalClose.close label depth t) = PA194InternalClose.close label depth t) := by definability
  apply IsSemiterm.sigma1_induction hdef (n := depth) ?_ ?_ ?_ t ht
  · intro z hz; simp [PA194InternalClose.close, PA194InternalClose.construction, hz, lt_trans hz (lt_add_one depth)]
  · intro x; by_cases hx : label = x <;> simp [PA194InternalClose.close, PA194InternalClose.construction, hx, lt_add_one]
  · intro k g v hg hv ih
    have hv' := PA194InternalFormulaClose.close_vec_wellformed label depth k v hv
    simp only [PA194InternalClose.close, Language.TermRec.Construction.result_func' _ hg hv.isUTerm]
    change PA194InternalClose.construction.result ℒₒᵣ ![label,depth+1] (^func k g (PA194InternalClose.construction.resultVec ℒₒᵣ ![label,depth] k v)) = _
    rw [Language.TermRec.Construction.result_func' _ hg hv'.isUTerm]
    simp only [PA194InternalClose.construction, qqFunc_inj, true_and]
    apply nth_ext' k (Language.TermRec.Construction.resultVec_lh _ _ _ hv'.isUTerm) (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm)
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv'.isUTerm hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    change PA194InternalClose.close label (depth+1) (PA194InternalClose.close label depth v.[i]) = _
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    exact ih i hi

lemma close_vec_twice (label depth k v : M) (hv : IsSemitermVec ℒₒᵣ k depth v) :
    PA194InternalClose.construction.resultVec ℒₒᵣ ![label,depth+1] k
      (PA194InternalClose.construction.resultVec ℒₒᵣ ![label,depth] k v) =
    PA194InternalClose.construction.resultVec ℒₒᵣ ![label,depth] k v := by
  have hv' := PA194InternalFormulaClose.close_vec_wellformed label depth k v hv
  apply nth_ext' k (Language.TermRec.Construction.resultVec_lh _ _ _ hv'.isUTerm) (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm)
  intro i hi
  rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv'.isUTerm hi,
    Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
  exact close_term_twice label depth v.[i] (hv.nth hi)

lemma close_formula_twice (label depth φ : M) (hφ : IsSemiformula ℒₒᵣ depth φ) :
    PA194InternalFormulaClose.close label (depth+1) (PA194InternalFormulaClose.close label depth φ) = PA194InternalFormulaClose.close label depth φ := by
  haveI : 𝚺₁-Function₂ ((PA194InternalFormulaClose.construction (M := M)).result ℒₒᵣ) := PA194InternalFormulaClose.graph.to_definable
  have hdef : 𝚺₁-Relation (fun n φ : M => PA194InternalFormulaClose.close label (n+1) (PA194InternalFormulaClose.close label n φ) = PA194InternalFormulaClose.close label n φ) := by
    unfold PA194InternalFormulaClose.close
    definability
  apply IsSemiformula.sigma1_structural_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hφ
  · intro n k r v hr hv
    rw [PA194InternalFormulaClose.close_rel label n k r v hr hv.isUTerm,
      PA194InternalFormulaClose.close_rel label (n+1) k r _ hr (PA194InternalFormulaClose.close_vec_wellformed label n k v hv).isUTerm,
      close_vec_twice label n k v hv]
  · intro n k r v hr hv
    rw [PA194InternalFormulaClose.close_nrel label n k r v hr hv.isUTerm,
      PA194InternalFormulaClose.close_nrel label (n+1) k r _ hr (PA194InternalFormulaClose.close_vec_wellformed label n k v hv).isUTerm,
      close_vec_twice label n k v hv]
  · intro n; simp [PA194InternalFormulaClose.close_verum]
  · intro n; simp [PA194InternalFormulaClose.close_falsum]
  · intro n p q hp hq ihp ihq
    rw [PA194InternalFormulaClose.close_and label n p q hp.isUFormula hq.isUFormula,
      PA194InternalFormulaClose.close_and label (n+1) _ _ (PA194InternalFormulaClose.close_wellformed label n p hp).isUFormula (PA194InternalFormulaClose.close_wellformed label n q hq).isUFormula,
      ihp,ihq]
  · intro n p q hp hq ihp ihq
    rw [PA194InternalFormulaClose.close_or label n p q hp.isUFormula hq.isUFormula,
      PA194InternalFormulaClose.close_or label (n+1) _ _ (PA194InternalFormulaClose.close_wellformed label n p hp).isUFormula (PA194InternalFormulaClose.close_wellformed label n q hq).isUFormula,
      ihp,ihq]
  · intro n p hp ih
    rw [PA194InternalFormulaClose.close_all label n p hp.isUFormula,
      PA194InternalFormulaClose.close_all label (n+1) _ (PA194InternalFormulaClose.close_wellformed label (n+1) p hp).isUFormula,
      ih]
  · intro n p hp ih
    rw [PA194InternalFormulaClose.close_exs label n p hp.isUFormula,
      PA194InternalFormulaClose.close_exs label (n+1) _ (PA194InternalFormulaClose.close_wellformed label (n+1) p hp).isUFormula,
      ih]

lemma subst_extra_eq_self (n w p : M) (hp : IsSemiformula ℒₒᵣ n p)
    (hw : IsSemitermVec ℒₒᵣ (n+1) n w) (H : ∀ i < n, w.[i] = ^#i) : subst ℒₒᵣ w p = p := by
  revert w
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv w _ H
    simp only [substs_rel, qqRel_inj, true_and, hR, hv.isUTerm]
    apply nth_ext' k (by simp [*, hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, termSubst_eq_self (hv.nth hi) H]
  · intro n k R v hR hv w _ H
    simp only [substs_nrel, qqNRel_inj, true_and, hR, hv.isUTerm]
    apply nth_ext' k (by simp [*, hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, termSubst_eq_self (hv.nth hi) H]
  · intro n w _ _; simp
  · intro n w _ _; simp
  · intro n p q hp hq ihp ihq w hw H
    simp [*, hp.isUFormula, hq.isUFormula, ihp w hw H, ihq w hw H]
  · intro n p q hp hq ihp ihq w hw H
    simp [*, hp.isUFormula, hq.isUFormula, ihp w hw H, ihq w hw H]
  · intro n p hp ih w hw H
    have H' : ∀ i < n + 1, (qVec ℒₒᵣ w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [qVec]
      · have hi : i < n := by simpa using hi
        simp only [qVec, nth_adjoin_succ]
        rw [nth_termBShiftVec (by simpa [hw.lh] using hw.isUTerm) (by rw [hw.lh]; exact lt_trans hi (lt_add_one n))]
        simp [H i hi]
    have hw' : IsSemitermVec ℒₒᵣ ((n+1)+1) (n+1) (qVec ℒₒᵣ w) := by simpa [add_assoc,add_comm,add_left_comm] using hw.qVec
    simp [*, hp.isUFormula, ih (qVec ℒₒᵣ w) hw' H']
  · intro n p hp ih w hw H
    have H' : ∀ i < n + 1, (qVec ℒₒᵣ w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [qVec]
      · have hi : i < n := by simpa using hi
        simp only [qVec, nth_adjoin_succ]
        rw [nth_termBShiftVec (by simpa [hw.lh] using hw.isUTerm) (by rw [hw.lh]; exact lt_trans hi (lt_add_one n))]
        simp [H i hi]
    have hw' : IsSemitermVec ℒₒᵣ ((n+1)+1) (n+1) (qVec ℒₒᵣ w) := by simpa [add_assoc,add_comm,add_left_comm] using hw.qVec
    simp [*, hp.isUFormula, ih (qVec ℒₒᵣ w) hw' H']

lemma unbound_free (R : Bootstrapping.Formula M ℒₒᵣ) (S : Bootstrapping.Semiformula M ℒₒᵣ 1)
    (h : S.val = R.val) : S.free = R.shift := by
  apply Bootstrapping.Semiformula.ext
  change subst ℒₒᵣ ?[^&0] (shift ℒₒᵣ S.val) = shift ℒₒᵣ R.val
  rw [h]
  exact subst_extra_eq_self 0 ?[^&0] (shift ℒₒᵣ R.val) R.shift.isSemiformula (by simp) (by simp)

end models
end PA194SourceHead1Syntax
