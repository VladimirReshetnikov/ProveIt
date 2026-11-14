import PA194RenameDerivation
import PA194SourceAllPreservation
/-! Model-uniform preservation of the numerical source universal rule by
internal PA provability, via derivation renaming and close/reopen agreement. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000
namespace PA194SourceUniversalPreservation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194GenericRenameBase PA194GenericRenameAxiom PA194GenericRenameRules PA194RenameShiftCompatibility PA194RenameSubstitution PA194RenameContexts PA194ExpandedRename PA194SourceOutputWF
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def openingVec (n w : M) : Prop := IsSemitermVec ℒₒᵣ (n+1) n w ∧ (∀ i < n, w.[i] = ^#i) ∧ w.[n] = ^&0

lemma openingVec_qVec (n w : M) (hw : openingVec n w) : openingVec (n+1) (qVec ℒₒᵣ w) := by
  obtain ⟨hw,hi,hn⟩ := hw
  refine ⟨by simpa [add_assoc] using hw.qVec, ?_, ?_⟩
  · intro i h
    rcases zero_or_succ i with (rfl | ⟨i,rfl⟩)
    · simp [qVec]
    · have hi' : i < n := by simpa using h
      simp only [qVec,nth_adjoin_succ]
      rw [hw.lh, nth_termBShiftVec hw.isUTerm (lt_trans hi' (lt_add_one n)),hi i hi']
      simp
  · simp only [qVec,nth_adjoin_succ]
    rw [hw.lh, nth_termBShiftVec hw.isUTerm (lt_add_one n), hn]
    simp

lemma openingVec_zero : openingVec (0 : M) ?[^&0] := by simp [openingVec]

lemma term_agreement (label n w t : M) (ht : IsSemiterm ℒₒᵣ n t) (hw : openingVec n w) :
    renameTerm expandedGraph packedRen expandedGraph_correct (pair 0 (pair label (pair 1 1))) t =
      termSubst ℒₒᵣ w (termShift ℒₒᵣ (PA194InternalClose.close label n t)) := by
  haveI := term_definable expandedGraph packedRen expandedGraph_correct (pair 0 (pair label (pair 1 1)))
  haveI := PA194InternalClose.close_definable label n
  have hdef : 𝚺₁-Predicate (fun t : M =>
      renameTerm expandedGraph packedRen expandedGraph_correct (pair 0 (pair label (pair 1 1))) t =
      termSubst ℒₒᵣ w (termShift ℒₒᵣ (PA194InternalClose.close label n t))) := by
    definability
  apply IsSemiterm.sigma1_induction hdef (n := n) ?_ ?_ ?_ t ht
  · intro z hz
    rw [rename_bvar, PA194InternalClose.close, Language.TermRec.Construction.result_bvar]
    simp [PA194InternalClose.construction,hz,hw.2.1 z hz]
  · intro x
    rw [rename_fvar, PA194InternalClose.close, Language.TermRec.Construction.result_fvar]
    simp only [PA194InternalClose.construction,Matrix.cons_val_zero,Matrix.cons_val_one]
    by_cases h : label = x
    · simp [h,packedRen,ren,hw.2.2]
    · simp [h,packedRen,ren,eq_comm]
  · intro k g v hg hv ih
    rw [rename_func expandedGraph packedRen expandedGraph_correct _ k g v hg hv.isUTerm]
    change _ = termSubst ℒₒᵣ w (termShift ℒₒᵣ (PA194InternalClose.construction.result ℒₒᵣ ![label,n] (^func k g v)))
    rw [Language.TermRec.Construction.result_func' _ hg hv.isUTerm]
    change _ = termSubst ℒₒᵣ w (termShift ℒₒᵣ (^func k g (PA194InternalClose.construction.resultVec ℒₒᵣ ![label,n] k v)))
    have hclose := PA194InternalFormulaClose.close_vec_wellformed label n k v hv
    rw [termShift_func hg hclose.isUTerm, termSubst_func hg hclose.termShiftVec.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm)
      (by rw [len_termSubstVec hclose.termShiftVec.isUTerm])
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi,
      nth_termSubstVec hclose.termShiftVec.isUTerm hi,
      nth_termShiftVec hclose.isUTerm hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    exact ih i hi

lemma vec_agreement (label n w k v : M) (hv : IsSemitermVec ℒₒᵣ k n v) (hw : openingVec n w) :
    (termConstruction expandedGraph packedRen expandedGraph_correct).resultVec ℒₒᵣ ![pair 0 (pair label (pair 1 1))] k v =
      termSubstVec ℒₒᵣ k w (termShiftVec ℒₒᵣ k (PA194InternalClose.construction.resultVec ℒₒᵣ ![label,n] k v)) := by
  have hclose := PA194InternalFormulaClose.close_vec_wellformed label n k v hv
  apply nth_ext' k (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm)
    (by rw [len_termSubstVec hclose.termShiftVec.isUTerm])
  intro i hi
  rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi,
    nth_termSubstVec hclose.termShiftVec.isUTerm hi,
    nth_termShiftVec hclose.isUTerm hi,
    Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
  exact term_agreement label n w v.[i] (hv.nth hi) hw

lemma formula_agreement (label n φ : M) (hφ : IsSemiformula ℒₒᵣ n φ) : ∀ w,
    openingVec n w →
    renameFormula expandedGraph packedRen expandedGraph_correct (pair 0 (pair label (pair 1 1))) φ =
      subst ℒₒᵣ w (shift ℒₒᵣ (PA194InternalFormulaClose.close label n φ)) := by
  haveI := formula_definable expandedGraph packedRen expandedGraph_correct (pair 0 (pair label (pair 1 1)))
  haveI : 𝚺₁-Function₂ ((PA194InternalFormulaClose.construction (M := M)).result ℒₒᵣ) := PA194InternalFormulaClose.graph.to_definable
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hφ
  · unfold openingVec PA194InternalFormulaClose.close
    definability
  · intro n k r v hr hv w hw
    rw [rename_rel expandedGraph packedRen expandedGraph_correct _ k r v hr hv.isUTerm,
      PA194InternalFormulaClose.close_rel label n k r v hr hv.isUTerm]
    have hclose := PA194InternalFormulaClose.close_vec_wellformed label n k v hv
    rw [shift_rel hr hclose.isUTerm, substs_rel hr hclose.termShiftVec.isUTerm]
    simp only [qqRel_inj, true_and]
    exact vec_agreement label n w k v hv hw
  · intro n k r v hr hv w hw
    rw [rename_nrel expandedGraph packedRen expandedGraph_correct _ k r v hr hv.isUTerm,
      PA194InternalFormulaClose.close_nrel label n k r v hr hv.isUTerm]
    have hclose := PA194InternalFormulaClose.close_vec_wellformed label n k v hv
    rw [shift_nrel hr hclose.isUTerm, substs_nrel hr hclose.termShiftVec.isUTerm]
    simp only [qqNRel_inj, true_and]
    exact vec_agreement label n w k v hv hw
  · intro n w hw; simp [rename_verum,PA194InternalFormulaClose.close_verum]
  · intro n w hw; simp [rename_falsum,PA194InternalFormulaClose.close_falsum]
  · intro n φ ψ hφ hψ ihφ ihψ w hw
    have hcφ := PA194InternalFormulaClose.close_wellformed label n φ hφ
    have hcψ := PA194InternalFormulaClose.close_wellformed label n ψ hψ
    rw [rename_and expandedGraph packedRen expandedGraph_correct _ _ _ hφ.isUFormula hψ.isUFormula,
      PA194InternalFormulaClose.close_and label n φ ψ hφ.isUFormula hψ.isUFormula,
      shift_and hcφ.isUFormula hcψ.isUFormula,
      substs_and hcφ.isUFormula.shift hcψ.isUFormula.shift, ihφ w hw, ihψ w hw]
  · intro n φ ψ hφ hψ ihφ ihψ w hw
    have hcφ := PA194InternalFormulaClose.close_wellformed label n φ hφ
    have hcψ := PA194InternalFormulaClose.close_wellformed label n ψ hψ
    rw [rename_or expandedGraph packedRen expandedGraph_correct _ _ _ hφ.isUFormula hψ.isUFormula,
      PA194InternalFormulaClose.close_or label n φ ψ hφ.isUFormula hψ.isUFormula,
      shift_or hcφ.isUFormula hcψ.isUFormula,
      substs_or hcφ.isUFormula.shift hcψ.isUFormula.shift, ihφ w hw, ihψ w hw]
  · intro n φ hφ ih w hw
    have hcφ := PA194InternalFormulaClose.close_wellformed label (n+1) φ hφ
    rw [rename_all expandedGraph packedRen expandedGraph_correct _ _ hφ.isUFormula,
      PA194InternalFormulaClose.close_all label n φ hφ.isUFormula,
      shift_all hcφ.isUFormula, substs_all hcφ.isUFormula.shift, ih _ (openingVec_qVec n w hw)]
  · intro n φ hφ ih w hw
    have hcφ := PA194InternalFormulaClose.close_wellformed label (n+1) φ hφ
    rw [rename_exs expandedGraph packedRen expandedGraph_correct _ _ hφ.isUFormula,
      PA194InternalFormulaClose.close_exs label n φ hφ.isUFormula,
      shift_exs hcφ.isUFormula, substs_ex hcφ.isUFormula.shift, ih _ (openingVec_qVec n w hw)]

lemma initial_rename_agreement (label φ : M) (hφ : IsFormula ℒₒᵣ φ) :
    renameFormula expandedGraph packedRen expandedGraph_correct (pair 0 (pair label (pair 1 1))) φ =
      free ℒₒᵣ (PA194InternalFormulaClose.close label 0 φ) := by
  exact formula_agreement label 0 φ hφ ?[^&0] openingVec_zero

lemma renameSet_empty (param : M) :
    renameSet expandedGraph packedRen expandedGraph_correct param (∅ : M) = ∅ := by
  apply mem_ext; intro y
  simp [mem_renameSet_iff]

theorem reopen_provable (label φ : M) (hφ : IsFormula ℒₒᵣ φ)
    (hprov : Provable (𝗣𝗔 : ArithmeticTheory) φ) :
    Provable (𝗣𝗔 : ArithmeticTheory) (free ℒₒᵣ (PA194InternalFormulaClose.close label 0 φ)) := by
  have h := PA194RenameDerivation.derivable_rename (insert φ (∅ : M)) 0 label 1 1 hprov.toDerivable
  change Derivable (𝗣𝗔 : ArithmeticTheory)
    (renameSet expandedGraph packedRen expandedGraph_correct (pair 0 (pair label (pair 1 1))) (insert φ (∅ : M))) at h
  rw [renameSet_insert,renameSet_empty, initial_rename_agreement label φ hφ] at h
  exact h.toProvable

theorem source_universal_preservation (label body : M)
    (hbody : Provable (𝗣𝗔 : ArithmeticTheory) (π₁ (F fixedTranslation (fun _ => body)))) :
    Provable (𝗣𝗔 : ArithmeticTheory) (π₁ (F fixedTranslation (fun _ => 4*cantor body label+2))) := by
  apply PA194SourceAllPreservation.all_of_free label body
  exact reopen_provable label _ (fixed_all_wf body).1 hbody

#print axioms source_universal_preservation
#print axioms reopen_provable
#print axioms initial_rename_agreement
#print axioms formula_agreement
#print axioms term_agreement
#print axioms openingVec_qVec
end models
end PA194SourceUniversalPreservation
