import PA194SourceHead5Preservation
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace PA194SourceHead2Syntax
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


def swapVec (n w : M) : Prop := IsSemitermVec ℒₒᵣ (n+2) (n+2) w ∧
  (∀ i < n, w.[i] = ^#i) ∧ w.[n] = ^#(n+1) ∧ w.[n+1] = ^#n

lemma swapVec_qVec (n w : M) (hw : swapVec n w) : swapVec (n+1) (qVec ℒₒᵣ w) := by
  obtain ⟨hw,hi,hn,hn1⟩ := hw
  have ht : n+2 = n+1+1 := by norm_num [add_assoc]
  have hnlt : n < n+2 := by rw [ht]; exact lt_trans (lt_add_one n) (lt_add_one (n+1))
  have hn1lt : n+1 < n+2 := by rw [ht]; exact lt_add_one (n+1)
  refine ⟨by simpa [add_assoc,add_comm,add_left_comm] using hw.qVec, ?_, ?_, ?_⟩
  · intro i h
    rcases zero_or_succ i with (rfl | ⟨i,rfl⟩)
    · simp [qVec]
    · have hi' : i < n := by simpa using h
      simp only [qVec,nth_adjoin_succ]
      rw [hw.lh, nth_termBShiftVec hw.isUTerm (lt_trans hi' hnlt), hi i hi']
      simp
  · simp only [qVec,nth_adjoin_succ]
    rw [hw.lh, nth_termBShiftVec hw.isUTerm hnlt, hn]
    simp [add_assoc,add_comm,add_left_comm]
  · have he : n+1+1 = (n+1)+1 := rfl
    rw [he]
    simp only [qVec,nth_adjoin_succ]
    rw [hw.lh, nth_termBShiftVec hw.isUTerm hn1lt, hn1]
    simp [add_assoc,add_comm,add_left_comm]

lemma swapVec_zero : swapVec (0 : M) ?[^#1,^#0] := by simp [swapVec]

lemma close_swap_term (a b n w t : M) (hab : a ≠ b) (ht : IsSemiterm ℒₒᵣ n t) (hw : swapVec n w) :
    termSubst ℒₒᵣ w (PA194InternalClose.close a (n+1) (PA194InternalClose.close b n t)) =
      PA194InternalClose.close b (n+1) (PA194InternalClose.close a n t) := by
  haveI := PA194InternalClose.close_definable a n
  haveI := PA194InternalClose.close_definable b n
  haveI := PA194InternalClose.close_definable a (n+1)
  haveI := PA194InternalClose.close_definable b (n+1)
  have hdef : 𝚺₁-Predicate (fun t : M => termSubst ℒₒᵣ w (PA194InternalClose.close a (n+1) (PA194InternalClose.close b n t)) = PA194InternalClose.close b (n+1) (PA194InternalClose.close a n t)) := by definability
  apply IsSemiterm.sigma1_induction hdef (n := n) ?_ ?_ ?_ t ht
  · intro z hz
    simp [PA194InternalClose.close, PA194InternalClose.construction, hz, lt_trans hz (lt_add_one n), hw.2.1 z hz]
  · intro x
    by_cases ha : a=x <;> by_cases hb : b=x <;>
      simp [PA194InternalClose.close, PA194InternalClose.construction, ha, hb, hw.2.2.1, hw.2.2.2, lt_add_one] at *
  · intro k g v hg hv ih
    have hvb := PA194InternalFormulaClose.close_vec_wellformed b n k v hv
    have hva := PA194InternalFormulaClose.close_vec_wellformed a n k v hv
    simp only [PA194InternalClose.close, Language.TermRec.Construction.result_func' _ hg hv.isUTerm]
    change termSubst ℒₒᵣ w (PA194InternalClose.construction.result ℒₒᵣ ![a,n+1] (^func k g (PA194InternalClose.construction.resultVec ℒₒᵣ ![b,n] k v))) =
      PA194InternalClose.construction.result ℒₒᵣ ![b,n+1] (^func k g (PA194InternalClose.construction.resultVec ℒₒᵣ ![a,n] k v))
    rw [Language.TermRec.Construction.result_func' _ hg hvb.isUTerm,
      Language.TermRec.Construction.result_func' _ hg hva.isUTerm]
    change termSubst ℒₒᵣ w (^func k g (PA194InternalClose.construction.resultVec ℒₒᵣ ![a,n+1] k (PA194InternalClose.construction.resultVec ℒₒᵣ ![b,n] k v))) =
      ^func k g (PA194InternalClose.construction.resultVec ℒₒᵣ ![b,n+1] k (PA194InternalClose.construction.resultVec ℒₒᵣ ![a,n] k v))
    have hvba := PA194InternalFormulaClose.close_vec_wellformed a (n+1) k _ hvb
    rw [termSubst_func hg hvba.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec hvba.isUTerm])
      (Language.TermRec.Construction.resultVec_lh _ _ _ hva.isUTerm)
    intro i hi
    rw [nth_termSubstVec hvba.isUTerm hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hvb.isUTerm hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hva.isUTerm hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    exact ih i hi
lemma close_swap_vec (a b n w k v : M) (hab : a ≠ b) (hv : IsSemitermVec ℒₒᵣ k n v) (hw : swapVec n w) :
    termSubstVec ℒₒᵣ k w (PA194InternalClose.construction.resultVec ℒₒᵣ ![a,n+1] k (PA194InternalClose.construction.resultVec ℒₒᵣ ![b,n] k v)) =
      PA194InternalClose.construction.resultVec ℒₒᵣ ![b,n+1] k (PA194InternalClose.construction.resultVec ℒₒᵣ ![a,n] k v) := by
  have hvb := PA194InternalFormulaClose.close_vec_wellformed b n k v hv
  have hva := PA194InternalFormulaClose.close_vec_wellformed a n k v hv
  have hvba := PA194InternalFormulaClose.close_vec_wellformed a (n+1) k _ hvb
  apply nth_ext' k (by rw [len_termSubstVec hvba.isUTerm]) (Language.TermRec.Construction.resultVec_lh _ _ _ hva.isUTerm)
  intro i hi
  rw [nth_termSubstVec hvba.isUTerm hi,
    Language.TermRec.Construction.nth_resultVec _ _ _ hvb.isUTerm hi,
    Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi,
    Language.TermRec.Construction.nth_resultVec _ _ _ hva.isUTerm hi,
    Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
  exact close_swap_term a b n w v.[i] hab (hv.nth hi) hw

lemma close_swap_formula (a b n φ : M) (hab : a ≠ b) (hφ : IsSemiformula ℒₒᵣ n φ) : ∀ w,
    swapVec n w → subst ℒₒᵣ w (PA194InternalFormulaClose.close a (n+1) (PA194InternalFormulaClose.close b n φ)) =
      PA194InternalFormulaClose.close b (n+1) (PA194InternalFormulaClose.close a n φ) := by
  haveI : 𝚺₁-Function₂ ((PA194InternalFormulaClose.construction (M := M)).result ℒₒᵣ) := PA194InternalFormulaClose.graph.to_definable
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hφ
  · unfold swapVec PA194InternalFormulaClose.close
    definability
  · intro n k r v hr hv w hw
    have hvb := PA194InternalFormulaClose.close_vec_wellformed b n k v hv
    have hva := PA194InternalFormulaClose.close_vec_wellformed a n k v hv
    have hvba := PA194InternalFormulaClose.close_vec_wellformed a (n+1) k _ hvb
    rw [PA194InternalFormulaClose.close_rel b n k r v hr hv.isUTerm,
      PA194InternalFormulaClose.close_rel a (n+1) k r _ hr hvb.isUTerm,
      substs_rel hr hvba.isUTerm,
      PA194InternalFormulaClose.close_rel a n k r v hr hv.isUTerm,
      PA194InternalFormulaClose.close_rel b (n+1) k r _ hr hva.isUTerm,
      close_swap_vec a b n w k v hab hv hw]
  · intro n k r v hr hv w hw
    have hvb := PA194InternalFormulaClose.close_vec_wellformed b n k v hv
    have hva := PA194InternalFormulaClose.close_vec_wellformed a n k v hv
    have hvba := PA194InternalFormulaClose.close_vec_wellformed a (n+1) k _ hvb
    rw [PA194InternalFormulaClose.close_nrel b n k r v hr hv.isUTerm,
      PA194InternalFormulaClose.close_nrel a (n+1) k r _ hr hvb.isUTerm,
      substs_nrel hr hvba.isUTerm,
      PA194InternalFormulaClose.close_nrel a n k r v hr hv.isUTerm,
      PA194InternalFormulaClose.close_nrel b (n+1) k r _ hr hva.isUTerm,
      close_swap_vec a b n w k v hab hv hw]
  · intro n w hw; simp [PA194InternalFormulaClose.close_verum]
  · intro n w hw; simp [PA194InternalFormulaClose.close_falsum]
  · intro n p q hp hq ihp ihq w hw
    have hpb := PA194InternalFormulaClose.close_wellformed b n p hp
    have hqb := PA194InternalFormulaClose.close_wellformed b n q hq
    have hpa := PA194InternalFormulaClose.close_wellformed a n p hp
    have hqa := PA194InternalFormulaClose.close_wellformed a n q hq
    have hpba := PA194InternalFormulaClose.close_wellformed a (n+1) _ hpb
    have hqba := PA194InternalFormulaClose.close_wellformed a (n+1) _ hqb
    rw [PA194InternalFormulaClose.close_and b n p q hp.isUFormula hq.isUFormula,
      PA194InternalFormulaClose.close_and a (n+1) _ _ hpb.isUFormula hqb.isUFormula,
      substs_and hpba.isUFormula hqba.isUFormula,
      PA194InternalFormulaClose.close_and a n p q hp.isUFormula hq.isUFormula,
      PA194InternalFormulaClose.close_and b (n+1) _ _ hpa.isUFormula hqa.isUFormula,
      ihp w hw,ihq w hw]
  · intro n p q hp hq ihp ihq w hw
    have hpb := PA194InternalFormulaClose.close_wellformed b n p hp
    have hqb := PA194InternalFormulaClose.close_wellformed b n q hq
    have hpa := PA194InternalFormulaClose.close_wellformed a n p hp
    have hqa := PA194InternalFormulaClose.close_wellformed a n q hq
    have hpba := PA194InternalFormulaClose.close_wellformed a (n+1) _ hpb
    have hqba := PA194InternalFormulaClose.close_wellformed a (n+1) _ hqb
    rw [PA194InternalFormulaClose.close_or b n p q hp.isUFormula hq.isUFormula,
      PA194InternalFormulaClose.close_or a (n+1) _ _ hpb.isUFormula hqb.isUFormula,
      substs_or hpba.isUFormula hqba.isUFormula,
      PA194InternalFormulaClose.close_or a n p q hp.isUFormula hq.isUFormula,
      PA194InternalFormulaClose.close_or b (n+1) _ _ hpa.isUFormula hqa.isUFormula,
      ihp w hw,ihq w hw]
  · intro n p hp ih w hw
    have hpb := PA194InternalFormulaClose.close_wellformed b (n+1) p hp
    have hpa := PA194InternalFormulaClose.close_wellformed a (n+1) p hp
    have hpba := PA194InternalFormulaClose.close_wellformed a ((n+1)+1) _ hpb
    rw [PA194InternalFormulaClose.close_all b n p hp.isUFormula,
      PA194InternalFormulaClose.close_all a (n+1) _ hpb.isUFormula,
      substs_all hpba.isUFormula,
      PA194InternalFormulaClose.close_all a n p hp.isUFormula,
      PA194InternalFormulaClose.close_all b (n+1) _ hpa.isUFormula,
      ih _ (swapVec_qVec n w hw)]
  · intro n p hp ih w hw
    have hpb := PA194InternalFormulaClose.close_wellformed b (n+1) p hp
    have hpa := PA194InternalFormulaClose.close_wellformed a (n+1) p hp
    have hpba := PA194InternalFormulaClose.close_wellformed a ((n+1)+1) _ hpb
    rw [PA194InternalFormulaClose.close_exs b n p hp.isUFormula,
      PA194InternalFormulaClose.close_exs a (n+1) _ hpb.isUFormula,
      substs_ex hpba.isUFormula,
      PA194InternalFormulaClose.close_exs a n p hp.isUFormula,
      PA194InternalFormulaClose.close_exs b (n+1) _ hpa.isUFormula,
      ih _ (swapVec_qVec n w hw)]

#print axioms close_swap_formula
#print axioms swapVec_qVec
#print axioms close_swap_term
end models
end PA194SourceHead2Syntax
