import PA194RenameDerivation
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ReplacementOpening
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194GenericRenameBase PA194GenericRenameAxiom PA194GenericRenameRules PA194RenameShiftCompatibility PA194RenameSubstitution PA194RenameContexts PA194ExpandedRename
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

def replaceGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y x p. ∃ label, !pi₁Def label p ∧ ∃ target, !pi₂Def target p ∧
    (label = x → y = target) ∧ (¬ label = x → y = x)”

noncomputable def replaceMap (p x : M) : M := if π₁ p = x then π₂ p else x

lemma replaceGraph_correct (v : Fin 3 → M) :
    (M ⊧/v replaceGraph.val) ↔ v 0 = replaceMap (v 2) (v 1) := by
  simp [replaceGraph,replaceMap]
  split_ifs <;> simp_all

def openingVec (target n w : M) : Prop := IsSemitermVec ℒₒᵣ (n+1) n w ∧ (∀ i < n, w.[i] = ^#i) ∧ w.[n] = ^&target

lemma openingVec_qVec (target n w : M) (hw : openingVec target n w) : openingVec target (n+1) (qVec ℒₒᵣ w) := by
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

lemma openingVec_zero (target : M) : openingVec target (0 : M) ?[^&target] := by simp [openingVec]

lemma term_agreement (label target n w t : M) (ht : IsSemiterm ℒₒᵣ n t) (hw : openingVec target n w) :
    renameTerm replaceGraph replaceMap replaceGraph_correct (pair label target) t =
      termSubst ℒₒᵣ w ((PA194InternalClose.close label n t)) := by
  haveI := term_definable replaceGraph replaceMap replaceGraph_correct (pair label target)
  haveI := PA194InternalClose.close_definable label n
  have hdef : 𝚺₁-Predicate (fun t : M =>
      renameTerm replaceGraph replaceMap replaceGraph_correct (pair label target) t =
      termSubst ℒₒᵣ w ((PA194InternalClose.close label n t))) := by
    definability
  apply IsSemiterm.sigma1_induction hdef (n := n) ?_ ?_ ?_ t ht
  · intro z hz
    rw [rename_bvar, PA194InternalClose.close, Language.TermRec.Construction.result_bvar]
    simp [PA194InternalClose.construction,hz,hw.2.1 z hz]
  · intro x
    rw [rename_fvar, PA194InternalClose.close, Language.TermRec.Construction.result_fvar]
    simp only [PA194InternalClose.construction,Matrix.cons_val_zero,Matrix.cons_val_one]
    by_cases h : label = x
    · simp [h,replaceMap,hw.2.2]
    · simp [h,replaceMap,eq_comm]
  · intro k g v hg hv ih
    rw [rename_func replaceGraph replaceMap replaceGraph_correct _ k g v hg hv.isUTerm]
    change _ = termSubst ℒₒᵣ w (PA194InternalClose.construction.result ℒₒᵣ ![label,n] (^func k g v))
    rw [Language.TermRec.Construction.result_func' _ hg hv.isUTerm]
    change _ = termSubst ℒₒᵣ w (^func k g (PA194InternalClose.construction.resultVec ℒₒᵣ ![label,n] k v))
    have hclose := PA194InternalFormulaClose.close_vec_wellformed label n k v hv
    rw [termSubst_func hg hclose.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm)
      (by rw [len_termSubstVec hclose.isUTerm])
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi,
      nth_termSubstVec hclose.isUTerm hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    exact ih i hi

lemma vec_agreement (label target n w k v : M) (hv : IsSemitermVec ℒₒᵣ k n v) (hw : openingVec target n w) :
    (termConstruction replaceGraph replaceMap replaceGraph_correct).resultVec ℒₒᵣ ![pair label target] k v =
      termSubstVec ℒₒᵣ k w (PA194InternalClose.construction.resultVec ℒₒᵣ ![label,n] k v) := by
  have hclose := PA194InternalFormulaClose.close_vec_wellformed label n k v hv
  apply nth_ext' k (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm)
    (by rw [len_termSubstVec hclose.isUTerm])
  intro i hi
  rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi,
    nth_termSubstVec hclose.isUTerm hi,
    Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
  exact term_agreement label target n w v.[i] (hv.nth hi) hw

lemma formula_agreement (label target n φ : M) (hφ : IsSemiformula ℒₒᵣ n φ) : ∀ w,
    openingVec target n w →
    renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) φ =
      subst ℒₒᵣ w ((PA194InternalFormulaClose.close label n φ)) := by
  haveI := formula_definable replaceGraph replaceMap replaceGraph_correct (pair label target)
  haveI : 𝚺₁-Function₂ ((PA194InternalFormulaClose.construction (M := M)).result ℒₒᵣ) := PA194InternalFormulaClose.graph.to_definable
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hφ
  · unfold openingVec PA194InternalFormulaClose.close
    definability
  · intro n k r v hr hv w hw
    rw [rename_rel replaceGraph replaceMap replaceGraph_correct _ k r v hr hv.isUTerm,
      PA194InternalFormulaClose.close_rel label n k r v hr hv.isUTerm]
    have hclose := PA194InternalFormulaClose.close_vec_wellformed label n k v hv
    rw [substs_rel hr hclose.isUTerm]
    simp only [qqRel_inj, true_and]
    exact vec_agreement label target n w k v hv hw
  · intro n k r v hr hv w hw
    rw [rename_nrel replaceGraph replaceMap replaceGraph_correct _ k r v hr hv.isUTerm,
      PA194InternalFormulaClose.close_nrel label n k r v hr hv.isUTerm]
    have hclose := PA194InternalFormulaClose.close_vec_wellformed label n k v hv
    rw [substs_nrel hr hclose.isUTerm]
    simp only [qqNRel_inj, true_and]
    exact vec_agreement label target n w k v hv hw
  · intro n w hw; simp [rename_verum,PA194InternalFormulaClose.close_verum]
  · intro n w hw; simp [rename_falsum,PA194InternalFormulaClose.close_falsum]
  · intro n φ ψ hφ hψ ihφ ihψ w hw
    have hcφ := PA194InternalFormulaClose.close_wellformed label n φ hφ
    have hcψ := PA194InternalFormulaClose.close_wellformed label n ψ hψ
    rw [rename_and replaceGraph replaceMap replaceGraph_correct _ _ _ hφ.isUFormula hψ.isUFormula,
      PA194InternalFormulaClose.close_and label n φ ψ hφ.isUFormula hψ.isUFormula,
      substs_and hcφ.isUFormula hcψ.isUFormula, ihφ w hw, ihψ w hw]
  · intro n φ ψ hφ hψ ihφ ihψ w hw
    have hcφ := PA194InternalFormulaClose.close_wellformed label n φ hφ
    have hcψ := PA194InternalFormulaClose.close_wellformed label n ψ hψ
    rw [rename_or replaceGraph replaceMap replaceGraph_correct _ _ _ hφ.isUFormula hψ.isUFormula,
      PA194InternalFormulaClose.close_or label n φ ψ hφ.isUFormula hψ.isUFormula,
      substs_or hcφ.isUFormula hcψ.isUFormula, ihφ w hw, ihψ w hw]
  · intro n φ hφ ih w hw
    have hcφ := PA194InternalFormulaClose.close_wellformed label (n+1) φ hφ
    rw [rename_all replaceGraph replaceMap replaceGraph_correct _ _ hφ.isUFormula,
      PA194InternalFormulaClose.close_all label n φ hφ.isUFormula,
      substs_all hcφ.isUFormula, ih _ (openingVec_qVec target n w hw)]
  · intro n φ hφ ih w hw
    have hcφ := PA194InternalFormulaClose.close_wellformed label (n+1) φ hφ
    rw [rename_exs replaceGraph replaceMap replaceGraph_correct _ _ hφ.isUFormula,
      PA194InternalFormulaClose.close_exs label n φ hφ.isUFormula,
      substs_ex hcφ.isUFormula, ih _ (openingVec_qVec target n w hw)]


lemma specialization_agreement (label target φ : M) (hφ : IsFormula ℒₒᵣ φ) :
    renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) φ =
      substs1 ℒₒᵣ (^&target) (PA194InternalFormulaClose.close label 0 φ) := by
  exact formula_agreement label target 0 φ hφ ?[^&target] (openingVec_zero target)

#print axioms specialization_agreement
#print axioms formula_agreement
end models
end PA194ReplacementOpening
