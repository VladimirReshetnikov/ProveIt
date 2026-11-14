import PA194SourceHead5Preservation
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace PA194CloseSubstitution
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



lemma close_term_bshift (label depth t : M) (ht : IsSemiterm ℒₒᵣ depth t) :
    PA194InternalClose.close label (depth+1) (termBShift ℒₒᵣ t) =
      termBShift ℒₒᵣ (PA194InternalClose.close label depth t) := by
  haveI := PA194InternalClose.close_definable label depth
  haveI := PA194InternalClose.close_definable label (depth+1)
  have hdef : 𝚺₁-Predicate (fun t : M => PA194InternalClose.close label (depth+1) (termBShift ℒₒᵣ t) = termBShift ℒₒᵣ (PA194InternalClose.close label depth t)) := by definability
  apply IsSemiterm.sigma1_induction hdef (n := depth) ?_ ?_ ?_ t ht
  · intro z hz
    have hz' : z+1 < depth+1 := (add_lt_add_iff_right 1).mpr hz
    simp [PA194InternalClose.close,PA194InternalClose.construction,hz,hz']
  · intro x
    by_cases hx : label=x <;> simp [PA194InternalClose.close,PA194InternalClose.construction,hx]
  · intro k g v hg hv ih
    have hc := PA194InternalFormulaClose.close_vec_wellformed label depth k v hv
    rw [termBShift_func hg hv.isUTerm]
    change PA194InternalClose.construction.result ℒₒᵣ ![label,depth+1] (^func k g (termBShiftVec ℒₒᵣ k v)) = _
    rw [Language.TermRec.Construction.result_func' _ hg hv.isUTerm.termBShiftVec]
    change ^func k g (PA194InternalClose.construction.resultVec ℒₒᵣ ![label,depth+1] k (termBShiftVec ℒₒᵣ k v)) = _
    change _ = termBShift ℒₒᵣ (PA194InternalClose.construction.result ℒₒᵣ ![label,depth] (^func k g v))
    rw [Language.TermRec.Construction.result_func' _ hg hv.isUTerm]
    change _ = termBShift ℒₒᵣ (^func k g (PA194InternalClose.construction.resultVec ℒₒᵣ ![label,depth] k v))
    rw [termBShift_func hg hc.isUTerm]
    simp only [qqFunc_inj,true_and]
    apply nth_ext' k (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm.termBShiftVec)
      (by rw [len_termBShiftVec hc.isUTerm])
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm.termBShiftVec hi,
      nth_termBShiftVec hc.isUTerm hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi,
      nth_termBShiftVec hv.isUTerm hi]
    exact ih i hi

noncomputable def closeVec (label depth k v : M) : M :=
  PA194InternalClose.construction.resultVec ℒₒᵣ ![label,depth] k v

lemma closeVec_q (label depth k v : M) (hv : IsSemitermVec ℒₒᵣ k depth v) :
    closeVec label (depth+1) (k+1) (qVec ℒₒᵣ v) = qVec ℒₒᵣ (closeVec label depth k v) := by
  have hc := PA194InternalFormulaClose.close_vec_wellformed label depth k v hv
  have hq : IsSemitermVec ℒₒᵣ (k+1) (depth+1) (qVec ℒₒᵣ v) := hv.qVec
  unfold closeVec
  apply nth_ext' (k+1) (Language.TermRec.Construction.resultVec_lh _ _ _ hq.isUTerm) (by simp only [qVec,len_adjoin]; rw [hc.lh, len_termBShiftVec hc.isUTerm])
  intro i hi
  rw [Language.TermRec.Construction.nth_resultVec _ _ _ hq.isUTerm hi]
  rcases zero_or_succ i with (rfl | ⟨i,rfl⟩)
  · simp [qVec,PA194InternalClose.close,PA194InternalClose.construction]
  · have hi' : i < k := by simpa using hi
    simp only [qVec,nth_adjoin_succ]
    rw [hv.lh, nth_termBShiftVec hv.isUTerm hi',
      Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm,
      nth_termBShiftVec hc.isUTerm hi',
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi']
    exact close_term_bshift label depth v.[i] (hv.nth hi')

lemma close_term_subst_fixed (label depth k w t : M)
    (ht : IsSemiterm ℒₒᵣ k t) (hw : IsSemitermVec ℒₒᵣ k depth w)
    (hf : termShift ℒₒᵣ t = t) :
    PA194InternalClose.close label depth (termSubst ℒₒᵣ w t) =
      termSubst ℒₒᵣ (closeVec label depth k w) t := by
  haveI := PA194InternalClose.close_definable label depth
  haveI : 𝚺₁-Function₁ (fun t : M => termSubst ℒₒᵣ w t) := by definability
  have hc := PA194InternalFormulaClose.close_vec_wellformed label depth k w hw
  have hdef : 𝚺₁-Predicate (fun t : M => termShift ℒₒᵣ t = t →
    PA194InternalClose.close label depth (termSubst ℒₒᵣ w t) = termSubst ℒₒᵣ (closeVec label depth k w) t) := by definability
  revert hf
  apply IsSemiterm.sigma1_induction hdef (n := k) ?_ ?_ ?_ t ht
  · intro z hz _
    rw [termSubst_bvar,termSubst_bvar]
    unfold closeVec
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hw.isUTerm hz]
    rfl
  · intro x hf
    simp only [termShift_fvar,qqFvar_inj] at hf
    exact False.elim ((ne_of_lt (lt_add_one x)) hf.symm)
  · intro m g v hg hv ih hf
    rw [termShift_func hg hv.isUTerm] at hf
    have hvfixed : termShiftVec ℒₒᵣ m v = v := by simpa using hf
    rw [termSubst_func hg hv.isUTerm]
    change PA194InternalClose.construction.result ℒₒᵣ ![label,depth] (^func m g (termSubstVec ℒₒᵣ m w v)) = _
    rw [Language.TermRec.Construction.result_func' _ hg (hw.termSubstVec hv).isUTerm]
    change ^func m g (PA194InternalClose.construction.resultVec ℒₒᵣ ![label,depth] m (termSubstVec ℒₒᵣ m w v)) = _
    rw [termSubst_func hg hv.isUTerm]
    simp only [qqFunc_inj,true_and]
    apply nth_ext' m (Language.TermRec.Construction.resultVec_lh _ _ _ (hw.termSubstVec hv).isUTerm)
      (by rw [len_termSubstVec hv.isUTerm])
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi, nth_termSubstVec hv.isUTerm hi]
    apply ih i hi
    have hh := congrArg (fun z : M => z.[i]) hvfixed
    simpa [nth_termShiftVec hv.isUTerm hi] using hh

lemma close_vec_subst_fixed (label depth k w m v : M)
    (hv : IsSemitermVec ℒₒᵣ m k v) (hw : IsSemitermVec ℒₒᵣ k depth w)
    (hf : termShiftVec ℒₒᵣ m v = v) :
    closeVec label depth m (termSubstVec ℒₒᵣ m w v) =
      termSubstVec ℒₒᵣ m (closeVec label depth k w) v := by
  unfold closeVec
  apply nth_ext' m (Language.TermRec.Construction.resultVec_lh _ _ _ (hw.termSubstVec hv).isUTerm)
    (by rw [len_termSubstVec hv.isUTerm])
  intro i hi
  rw [Language.TermRec.Construction.nth_resultVec _ _ _ (hw.termSubstVec hv).isUTerm hi,
    nth_termSubstVec hv.isUTerm hi, nth_termSubstVec hv.isUTerm hi]
  apply close_term_subst_fixed label depth k w v.[i] (hv.nth hi) hw
  have hh := congrArg (fun z : M => z.[i]) hf
  simpa [nth_termShiftVec hv.isUTerm hi] using hh

lemma closeVec_definable (label : M) : 𝚺₁-Function₃ (fun depth k v : M => closeVec label depth k v) := by
  have hg : 𝚺₁.DefinableFunction (fun v : Fin 4 → M =>
      (PA194InternalClose.construction (M := M)).resultVec ℒₒᵣ (v ·.succ.succ) (v 0) (v 1)) :=
    HierarchySymbol.Defined.to_definable _ ((PA194InternalClose.construction (M := M)).resultVec_defined (L := ℒₒᵣ))
  have hi : ∀ j : Fin 4, 𝚺₁.DefinableFunction (fun v : Fin 3 → M => ![v 1,v 2,label,v 0] j) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact HierarchySymbol.DefinableFunction.var 1
    · refine Fin.cases ?_ (fun l => ?_) k
      · exact HierarchySymbol.DefinableFunction.var 2
      · refine Fin.cases ?_ (fun l => ?_) l
        · exact HierarchySymbol.DefinableFunction.const label
        · exact Fin.cases (HierarchySymbol.DefinableFunction.var 0) (fun x => Fin.elim0 x) l
  have h := HierarchySymbol.DefinableFunction.substitution hg hi
  change 𝚺₁.DefinableFunction (fun v : Fin 3 → M => closeVec label (v 0) (v 1) (v 2))
  convert h using 1
  funext v
  unfold closeVec
  congr 1

lemma close_formula_subst_fixed (label k φ : M) (hφ : IsSemiformula ℒₒᵣ k φ) : ∀ depth w,
    IsSemitermVec ℒₒᵣ k depth w → shift ℒₒᵣ φ = φ →
      PA194InternalFormulaClose.close label depth (subst ℒₒᵣ w φ) =
        subst ℒₒᵣ (closeVec label depth k w) φ := by
  haveI := closeVec_definable label
  haveI : 𝚺₁-Function₂ ((PA194InternalFormulaClose.construction (M := M)).result ℒₒᵣ) := PA194InternalFormulaClose.graph.to_definable
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hφ
  · unfold PA194InternalFormulaClose.close
    definability
  · intro n k r v hr hv depth w hw hf
    rw [shift_rel hr hv.isUTerm] at hf
    have hvfixed : termShiftVec ℒₒᵣ k v = v := by simpa using hf
    have hc := PA194InternalFormulaClose.close_vec_wellformed label depth n w hw
    rw [substs_rel hr hv.isUTerm, PA194InternalFormulaClose.close_rel label depth k r _ hr (hw.termSubstVec hv).isUTerm,
      substs_rel hr hv.isUTerm]
    exact congrArg (fun u : M => ^rel k r u) (close_vec_subst_fixed label depth n w k v hv hw hvfixed)
  · intro n k r v hr hv depth w hw hf
    rw [shift_nrel hr hv.isUTerm] at hf
    have hvfixed : termShiftVec ℒₒᵣ k v = v := by simpa using hf
    have hc := PA194InternalFormulaClose.close_vec_wellformed label depth n w hw
    rw [substs_nrel hr hv.isUTerm, PA194InternalFormulaClose.close_nrel label depth k r _ hr (hw.termSubstVec hv).isUTerm,
      substs_nrel hr hv.isUTerm]
    exact congrArg (fun u : M => ^nrel k r u) (close_vec_subst_fixed label depth n w k v hv hw hvfixed)
  · intro n depth w hw hf; simp [PA194InternalFormulaClose.close_verum]
  · intro n depth w hw hf; simp [PA194InternalFormulaClose.close_falsum]
  · intro n p q hp hq ihp ihq depth w hw hf
    rw [shift_and hp.isUFormula hq.isUFormula] at hf
    have hh : shift ℒₒᵣ p = p ∧ shift ℒₒᵣ q = q := by simpa using hf
    rw [substs_and hp.isUFormula hq.isUFormula,
      PA194InternalFormulaClose.close_and label depth _ _ (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      substs_and hp.isUFormula hq.isUFormula, ihp depth w hw hh.1,ihq depth w hw hh.2]
  · intro n p q hp hq ihp ihq depth w hw hf
    rw [shift_or hp.isUFormula hq.isUFormula] at hf
    have hh : shift ℒₒᵣ p = p ∧ shift ℒₒᵣ q = q := by simpa using hf
    rw [substs_or hp.isUFormula hq.isUFormula,
      PA194InternalFormulaClose.close_or label depth _ _ (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      substs_or hp.isUFormula hq.isUFormula, ihp depth w hw hh.1,ihq depth w hw hh.2]
  · intro n p hp ih depth w hw hf
    rw [shift_all hp.isUFormula] at hf
    have hh : shift ℒₒᵣ p = p := by simpa using hf
    rw [substs_all hp.isUFormula,
      PA194InternalFormulaClose.close_all label depth _ (hp.subst hw.qVec).isUFormula,
      substs_all hp.isUFormula,
      ih (depth+1) (qVec ℒₒᵣ w) hw.qVec hh, closeVec_q label depth n w hw]
  · intro n p hp ih depth w hw hf
    rw [shift_exs hp.isUFormula] at hf
    have hh : shift ℒₒᵣ p = p := by simpa using hf
    rw [substs_ex hp.isUFormula,
      PA194InternalFormulaClose.close_exs label depth _ (hp.subst hw.qVec).isUFormula,
      substs_ex hp.isUFormula,
      ih (depth+1) (qVec ℒₒᵣ w) hw.qVec hh, closeVec_q label depth n w hw]

lemma closeVec_two (label depth t u : M) (ht : IsSemiterm ℒₒᵣ depth t) (hu : IsSemiterm ℒₒᵣ depth u) :
    closeVec label depth 2 ?[t,u] = ?[PA194InternalClose.close label depth t, PA194InternalClose.close label depth u] := by
  unfold closeVec
  rw [show (2 : M) = 1+1 by norm_num,
    Language.TermRec.Construction.resultVec_cons _ _ _ (by simp [hu.isUTerm]) ht.isUTerm,
    show (1 : M) = 0+1 by simp,
    Language.TermRec.Construction.resultVec_cons _ _ _ (by simp) hu.isUTerm]
  simp [PA194InternalClose.close]

lemma close_bit_template (label depth t u : M) (ht : IsSemiterm ℒₒᵣ depth t) (hu : IsSemiterm ℒₒᵣ depth u) :
    PA194InternalFormulaClose.close label depth (subst ℒₒᵣ ?[t,u] (PA194SourceHead5Preservation.bitBase (M := M)).val) =
      subst ℒₒᵣ ?[PA194InternalClose.close label depth t,PA194InternalClose.close label depth u] (PA194SourceHead5Preservation.bitBase (M := M)).val := by
  have hh := close_formula_subst_fixed label 2 (PA194SourceHead5Preservation.bitBase (M := M)).val
    (PA194SourceHead5Preservation.bitBase (M := M)).isSemiformula depth ?[t,u]
    (by simp [ht,hu]) PA194SourceHead5Preservation.bitBase_fixed
  rw [closeVec_two label depth t u ht hu] at hh
  exact hh

noncomputable def closedBit (label a b : M) : Bootstrapping.Semiformula M ℒₒᵣ 1 :=
  (PA194SourceHead5Preservation.bitBase (M := M)).subst ![
    if label=b then Bootstrapping.Semiterm.bvar 0 else Bootstrapping.Semiterm.fvar b,
    if label=a then Bootstrapping.Semiterm.bvar 0 else Bootstrapping.Semiterm.fvar a]

lemma close_bitFormula (label a b : M) :
    PA194InternalFormulaClose.close label 0 (PA194SourceEqualityPreservation.bitFormula a b).val = (closedBit label a b).val := by
  have h := close_bit_template label 0 (^&b) (^&a) (by simp) (by simp)
  simp only [PA194InternalClose.close,Language.TermRec.Construction.result_fvar,
    PA194InternalClose.construction,Matrix.cons_val_zero,Matrix.cons_val_one] at h
  simpa [closedBit,PA194SourceEqualityPreservation.bitFormula,PA194SourceHead5Preservation.bitBase,
      Bootstrapping.Semiformula.val_substs,Bootstrapping.SemitermVec.val,matrixToVec,adjoin_def,
      Bootstrapping.Semiterm.bvar,Bootstrapping.Semiterm.fvar,apply_ite] using h

lemma close_bit_point (b c : M) (hcb : c ≠ b) :
    PA194InternalFormulaClose.close c 0 (PA194SourceEqualityPreservation.bitFormula c b).val =
      ((PA194SourceHead5Preservation.bitBase (M := M)).subst (![Bootstrapping.Semiterm.fvar b,Bootstrapping.Semiterm.bvar 0] : Bootstrapping.SemitermVec M ℒₒᵣ 2 1)).val := by
  rw [close_bitFormula]
  simp [closedBit,hcb]

lemma close_bit_twice_cross (b c : M) (hcb : c ≠ b) :
    PA194InternalFormulaClose.close c 1 (PA194InternalFormulaClose.close b 0 (PA194SourceEqualityPreservation.bitFormula c b).val) =
      ((PA194SourceHead5Preservation.bitBase (M := M)).subst (![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 1] : Bootstrapping.SemitermVec M ℒₒᵣ 2 2)).val := by
  rw [close_bitFormula]
  have h := close_bit_template c 1 (^#0) (^&c) (by simp) (by simp)
  simp only [PA194InternalClose.close, Language.TermRec.Construction.result_bvar, Language.TermRec.Construction.result_fvar,
    PA194InternalClose.construction,Matrix.cons_val_zero,Matrix.cons_val_one] at h
  simpa [closedBit,PA194SourceHead5Preservation.bitBase,Bootstrapping.Semiformula.val_substs,
    Bootstrapping.SemitermVec.val,matrixToVec,adjoin_def,Bootstrapping.Semiterm.bvar,Bootstrapping.Semiterm.fvar,
    hcb,Ne.symm hcb] using h

lemma close_bit_twice_diag (b c : M) :
    PA194InternalFormulaClose.close c 1 (PA194InternalFormulaClose.close b 0 (PA194SourceEqualityPreservation.bitFormula b b).val) =
      ((PA194SourceHead5Preservation.bitBase (M := M)).subst (![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 0] : Bootstrapping.SemitermVec M ℒₒᵣ 2 2)).val := by
  rw [close_bitFormula]
  have h := close_bit_template c 1 (^#0) (^#0) (by simp) (by simp)
  simp only [PA194InternalClose.close, Language.TermRec.Construction.result_bvar,
    PA194InternalClose.construction,Matrix.cons_val_zero,Matrix.cons_val_one] at h
  simpa [closedBit,PA194SourceHead5Preservation.bitBase,Bootstrapping.Semiformula.val_substs,
    Bootstrapping.SemitermVec.val,matrixToVec,adjoin_def,Bootstrapping.Semiterm.bvar] using h

#print axioms close_bit_twice_cross
#print axioms close_bit_twice_diag
#print axioms close_bit_point
#print axioms close_bitFormula
#print axioms close_bit_template
#print axioms close_formula_subst_fixed
#print axioms closeVec_definable
#print axioms close_vec_subst_fixed
#print axioms close_term_subst_fixed
#print axioms closeVec_q
#print axioms close_term_bshift
end models
end PA194CloseSubstitution
