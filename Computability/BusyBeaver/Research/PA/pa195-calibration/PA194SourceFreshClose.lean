import PA194SourceHead5Preservation
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace PA194SourceFreshClose
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


lemma term_close_keeps_fixed (label target binder depth t : M) (hne : label ≠ target)
    (ht : IsSemiterm ℒₒᵣ depth t)
    (hf : renameTerm replaceGraph replaceMap replaceGraph_correct (pair label target) t = t) :
    renameTerm replaceGraph replaceMap replaceGraph_correct (pair label target) (PA194InternalClose.close binder depth t) = PA194InternalClose.close binder depth t := by
  haveI := term_definable replaceGraph replaceMap replaceGraph_correct (pair label target)
  haveI := PA194InternalClose.close_definable binder depth
  have hdef : 𝚺₁-Predicate (fun t : M => renameTerm replaceGraph replaceMap replaceGraph_correct (pair label target) t = t →
    renameTerm replaceGraph replaceMap replaceGraph_correct (pair label target) (PA194InternalClose.close binder depth t) = PA194InternalClose.close binder depth t) := by definability
  revert hf
  apply IsSemiterm.sigma1_induction hdef (n := depth) ?_ ?_ ?_ t ht
  · intro z hz _; simp [PA194InternalClose.close, PA194InternalClose.construction, hz, rename_bvar]
  · intro x hx
    rw [rename_fvar] at hx
    have hfix : (if label=x then target else x) = x := by simpa [replaceMap] using hx
    have hnot : label ≠ x := by
      intro he; subst x; simp at hfix; exact hne hfix.symm
    by_cases hb : binder=x <;>
      simp [PA194InternalClose.close, PA194InternalClose.construction, hb, rename_bvar, rename_fvar,replaceMap,hnot]
  · intro k g v hg hv ih hf
    rw [rename_func replaceGraph replaceMap replaceGraph_correct _ k g v hg hv.isUTerm] at hf
    have hvfixed : (termConstruction replaceGraph replaceMap replaceGraph_correct).resultVec ℒₒᵣ ![pair label target] k v = v := by simpa using hf
    have hc := PA194InternalFormulaClose.close_vec_wellformed binder depth k v hv
    change renameTerm replaceGraph replaceMap replaceGraph_correct (pair label target) (PA194InternalClose.construction.result ℒₒᵣ ![binder,depth] (^func k g v)) = _
    rw [Language.TermRec.Construction.result_func' _ hg hv.isUTerm]
    change renameTerm replaceGraph replaceMap replaceGraph_correct (pair label target) (^func k g (PA194InternalClose.construction.resultVec ℒₒᵣ ![binder,depth] k v)) = _
    rw [rename_func replaceGraph replaceMap replaceGraph_correct _ k g _ hg hc.isUTerm]
    simp only [PA194InternalClose.close, Language.TermRec.Construction.result_func' _ hg hv.isUTerm, PA194InternalClose.construction, qqFunc_inj, true_and]
    apply nth_ext' k (Language.TermRec.Construction.resultVec_lh _ _ _ hc.isUTerm) (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm)
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hc.isUTerm hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    change renameTerm replaceGraph replaceMap replaceGraph_correct (pair label target) (PA194InternalClose.close binder depth v.[i]) = _
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    apply ih i hi
    have hh := congrArg (fun z : M => z.[i]) hvfixed
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi] at hh
    exact hh

lemma close_vec_keeps_fixed (label target binder depth k v : M) (hne : label ≠ target)
    (hv : IsSemitermVec ℒₒᵣ k depth v)
    (hf : (termConstruction replaceGraph replaceMap replaceGraph_correct).resultVec ℒₒᵣ ![pair label target] k v = v) :
    (termConstruction replaceGraph replaceMap replaceGraph_correct).resultVec ℒₒᵣ ![pair label target] k
      (PA194InternalClose.construction.resultVec ℒₒᵣ ![binder,depth] k v) =
      PA194InternalClose.construction.resultVec ℒₒᵣ ![binder,depth] k v := by
  have hc := PA194InternalFormulaClose.close_vec_wellformed binder depth k v hv
  apply nth_ext' k (Language.TermRec.Construction.resultVec_lh _ _ _ hc.isUTerm) (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm)
  intro i hi
  rw [Language.TermRec.Construction.nth_resultVec _ _ _ hc.isUTerm hi,
    Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
  apply term_close_keeps_fixed label target binder depth v.[i] hne (hv.nth hi)
  have hh := congrArg (fun z : M => z.[i]) hf
  rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi] at hh
  exact hh

lemma formula_close_keeps_fixed (label target binder depth p : M) (hne : label ≠ target)
    (hp : IsSemiformula ℒₒᵣ depth p)
    (hf : renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) p = p) :
    renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) (PA194InternalFormulaClose.close binder depth p) = PA194InternalFormulaClose.close binder depth p := by
  haveI := formula_definable replaceGraph replaceMap replaceGraph_correct (pair label target)
  haveI : 𝚺₁-Function₂ ((PA194InternalFormulaClose.construction (M := M)).result ℒₒᵣ) := PA194InternalFormulaClose.graph.to_definable
  have hdef : 𝚺₁-Relation (fun depth p : M => renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) p = p →
      renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) (PA194InternalFormulaClose.close binder depth p) = PA194InternalFormulaClose.close binder depth p) := by
    unfold PA194InternalFormulaClose.close
    definability
  revert hf
  apply IsSemiformula.sigma1_structural_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro n k r v hr hv hf
    rw [rename_rel replaceGraph replaceMap replaceGraph_correct _ k r v hr hv.isUTerm] at hf
    have hvfixed : (termConstruction replaceGraph replaceMap replaceGraph_correct).resultVec ℒₒᵣ ![pair label target] k v = v := by simpa using hf
    have hc := PA194InternalFormulaClose.close_vec_wellformed binder n k v hv
    rw [PA194InternalFormulaClose.close_rel binder n k r v hr hv.isUTerm,
      rename_rel replaceGraph replaceMap replaceGraph_correct _ k r _ hr hc.isUTerm,
      close_vec_keeps_fixed label target binder n k v hne hv hvfixed]
  · intro n k r v hr hv hf
    rw [rename_nrel replaceGraph replaceMap replaceGraph_correct _ k r v hr hv.isUTerm] at hf
    have hvfixed : (termConstruction replaceGraph replaceMap replaceGraph_correct).resultVec ℒₒᵣ ![pair label target] k v = v := by simpa using hf
    have hc := PA194InternalFormulaClose.close_vec_wellformed binder n k v hv
    rw [PA194InternalFormulaClose.close_nrel binder n k r v hr hv.isUTerm,
      rename_nrel replaceGraph replaceMap replaceGraph_correct _ k r _ hr hc.isUTerm,
      close_vec_keeps_fixed label target binder n k v hne hv hvfixed]
  · intro n _; simp [PA194InternalFormulaClose.close_verum,rename_verum]
  · intro n _; simp [PA194InternalFormulaClose.close_falsum,rename_falsum]
  · intro n p q hp hq ihp ihq hf
    rw [rename_and replaceGraph replaceMap replaceGraph_correct _ p q hp.isUFormula hq.isUFormula] at hf
    have hh : renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) p = p ∧ renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) q = q := by simpa using hf
    have hcp := PA194InternalFormulaClose.close_wellformed binder n p hp
    have hcq := PA194InternalFormulaClose.close_wellformed binder n q hq
    rw [PA194InternalFormulaClose.close_and binder n p q hp.isUFormula hq.isUFormula,
      rename_and replaceGraph replaceMap replaceGraph_correct _ _ _ hcp.isUFormula hcq.isUFormula, ihp hh.1,ihq hh.2]
  · intro n p q hp hq ihp ihq hf
    rw [rename_or replaceGraph replaceMap replaceGraph_correct _ p q hp.isUFormula hq.isUFormula] at hf
    have hh : renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) p = p ∧ renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) q = q := by simpa using hf
    have hcp := PA194InternalFormulaClose.close_wellformed binder n p hp
    have hcq := PA194InternalFormulaClose.close_wellformed binder n q hq
    rw [PA194InternalFormulaClose.close_or binder n p q hp.isUFormula hq.isUFormula,
      rename_or replaceGraph replaceMap replaceGraph_correct _ _ _ hcp.isUFormula hcq.isUFormula, ihp hh.1,ihq hh.2]
  · intro n p hp ih hf
    rw [rename_all replaceGraph replaceMap replaceGraph_correct _ p hp.isUFormula] at hf
    have hh : renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) p = p := by simpa using hf
    have hc := PA194InternalFormulaClose.close_wellformed binder (n+1) p hp
    rw [PA194InternalFormulaClose.close_all binder n p hp.isUFormula,
      rename_all replaceGraph replaceMap replaceGraph_correct _ _ hc.isUFormula, ih hh]
  · intro n p hp ih hf
    rw [rename_exs replaceGraph replaceMap replaceGraph_correct _ p hp.isUFormula] at hf
    have hh : renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) p = p := by simpa using hf
    have hc := PA194InternalFormulaClose.close_wellformed binder (n+1) p hp
    rw [PA194InternalFormulaClose.close_exs binder n p hp.isUFormula,
      rename_exs replaceGraph replaceMap replaceGraph_correct _ _ hc.isUFormula, ih hh]

lemma term_close_of_fixed (label target depth t : M) (hne : label ≠ target)
    (ht : IsSemiterm ℒₒᵣ depth t)
    (hf : renameTerm replaceGraph replaceMap replaceGraph_correct (pair label target) t = t) :
    PA194InternalClose.close label depth t = t := by
  haveI := term_definable replaceGraph replaceMap replaceGraph_correct (pair label target)
  haveI := PA194InternalClose.close_definable label depth
  have hdef : 𝚺₁-Predicate (fun t : M => renameTerm replaceGraph replaceMap replaceGraph_correct (pair label target) t = t → PA194InternalClose.close label depth t = t) := by definability
  revert hf
  apply IsSemiterm.sigma1_induction hdef (n := depth) ?_ ?_ ?_ t ht
  · intro z hz _; simp [PA194InternalClose.close, PA194InternalClose.construction,hz]
  · intro x hx
    rw [rename_fvar] at hx
    have hfix : (if label=x then target else x) = x := by simpa [replaceMap] using hx
    have hnot : label ≠ x := by
      intro he; subst x; simp at hfix; exact hne hfix.symm
    simp [PA194InternalClose.close, PA194InternalClose.construction, hnot]
  · intro k g v hg hv ih hf
    rw [rename_func replaceGraph replaceMap replaceGraph_correct _ k g v hg hv.isUTerm] at hf
    have hvfixed : (termConstruction replaceGraph replaceMap replaceGraph_correct).resultVec ℒₒᵣ ![pair label target] k v = v := by simpa using hf
    change PA194InternalClose.construction.result ℒₒᵣ ![label,depth] (^func k g v) = _
    rw [Language.TermRec.Construction.result_func' _ hg hv.isUTerm]
    simp only [PA194InternalClose.construction, qqFunc_inj, true_and]
    apply nth_ext' k (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm) (by simpa using hv.lh)
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    change PA194InternalClose.close label depth v.[i] = v.[i]
    apply ih i hi
    have hh := congrArg (fun z : M => z.[i]) hvfixed
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi] at hh
    exact hh

lemma vec_close_of_fixed (label target depth k v : M) (hne : label ≠ target)
    (hv : IsSemitermVec ℒₒᵣ k depth v)
    (hf : (termConstruction replaceGraph replaceMap replaceGraph_correct).resultVec ℒₒᵣ ![pair label target] k v = v) :
    PA194InternalClose.construction.resultVec ℒₒᵣ ![label,depth] k v = v := by
  apply nth_ext' k (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm) (by simpa using hv.lh)
  intro i hi
  rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
  apply term_close_of_fixed label target depth v.[i] hne (hv.nth hi)
  have hh := congrArg (fun z : M => z.[i]) hf
  rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi] at hh
  exact hh

lemma formula_close_of_fixed (label target depth p : M) (hne : label ≠ target)
    (hp : IsSemiformula ℒₒᵣ depth p)
    (hf : renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) p = p) :
    PA194InternalFormulaClose.close label depth p = p := by
  haveI := formula_definable replaceGraph replaceMap replaceGraph_correct (pair label target)
  haveI : 𝚺₁-Function₂ ((PA194InternalFormulaClose.construction (M := M)).result ℒₒᵣ) := PA194InternalFormulaClose.graph.to_definable
  have hdef : 𝚺₁-Relation (fun depth p : M => renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) p = p → PA194InternalFormulaClose.close label depth p = p) := by
    unfold PA194InternalFormulaClose.close
    definability
  revert hf
  apply IsSemiformula.sigma1_structural_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro n k r v hr hv hf
    rw [rename_rel replaceGraph replaceMap replaceGraph_correct _ k r v hr hv.isUTerm] at hf
    have hvfixed : (termConstruction replaceGraph replaceMap replaceGraph_correct).resultVec ℒₒᵣ ![pair label target] k v = v := by simpa using hf
    rw [PA194InternalFormulaClose.close_rel label n k r v hr hv.isUTerm, vec_close_of_fixed label target n k v hne hv hvfixed]
  · intro n k r v hr hv hf
    rw [rename_nrel replaceGraph replaceMap replaceGraph_correct _ k r v hr hv.isUTerm] at hf
    have hvfixed : (termConstruction replaceGraph replaceMap replaceGraph_correct).resultVec ℒₒᵣ ![pair label target] k v = v := by simpa using hf
    rw [PA194InternalFormulaClose.close_nrel label n k r v hr hv.isUTerm, vec_close_of_fixed label target n k v hne hv hvfixed]
  · intro n _; simp [PA194InternalFormulaClose.close_verum]
  · intro n _; simp [PA194InternalFormulaClose.close_falsum]
  · intro n p q hp hq ihp ihq hf
    rw [rename_and replaceGraph replaceMap replaceGraph_correct _ p q hp.isUFormula hq.isUFormula] at hf
    have hh : renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) p = p ∧ renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) q = q := by simpa using hf
    rw [PA194InternalFormulaClose.close_and label n p q hp.isUFormula hq.isUFormula, ihp hh.1,ihq hh.2]
  · intro n p q hp hq ihp ihq hf
    rw [rename_or replaceGraph replaceMap replaceGraph_correct _ p q hp.isUFormula hq.isUFormula] at hf
    have hh : renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) p = p ∧ renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) q = q := by simpa using hf
    rw [PA194InternalFormulaClose.close_or label n p q hp.isUFormula hq.isUFormula, ihp hh.1,ihq hh.2]
  · intro n p hp ih hf
    rw [rename_all replaceGraph replaceMap replaceGraph_correct _ p hp.isUFormula] at hf
    have hh : renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) p = p := by simpa using hf
    rw [PA194InternalFormulaClose.close_all label n p hp.isUFormula, ih hh]
  · intro n p hp ih hf
    rw [rename_exs replaceGraph replaceMap replaceGraph_correct _ p hp.isUFormula] at hf
    have hh : renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) p = p := by simpa using hf
    rw [PA194InternalFormulaClose.close_exs label n p hp.isUFormula, ih hh]

#print axioms formula_close_of_fixed
#print axioms formula_close_keeps_fixed
#print axioms term_close_keeps_fixed
end models
end PA194SourceFreshClose
