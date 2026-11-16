import PA194PAeqTypedFreeBound
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ForwardTyped
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem atomFreeBound_quoteVec {n : Nat} (v : Fin 2 → SourceTerm n) :
    atomFreeBound 2 (SemitermVec.val fun i => (⌜v i⌝ : Bootstrapping.Semiterm V PA194PAeq.language n)) =
      (finFreeBound ((v 0).freeVariables ∪ (v 1).freeVariables) : V) := by
  have hvec : SemitermVec.val (fun i => (⌜v i⌝ : Bootstrapping.Semiterm V PA194PAeq.language n)) =
      (?[ (⌜v 0⌝ : V), (⌜v 1⌝ : V)] : V) := by
    simp [SemitermVec.val_succ,Semiterm.quote_def,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  rw [hvec]
  have h0 := quote_term_valid (V := V) (v 0)
  have h1 := quote_term_valid (V := V) (v 1)
  have hv1 : IsUTermVec PA194PAeq.language (1 : V) (?[⌜v 1⌝] : V) := by simp [h1]
  have hh := termFreeBoundVec_cons h0 hv1
  have hh' := termFreeBoundVec_cons h1 (show IsUTermVec PA194PAeq.language (0 : V) 0 by simp)
  have htail : termFreeBoundVec 1 (?[⌜v 1⌝] : V) = ?[termFreeBound (⌜v 1⌝ : V)] := by simpa using hh'
  have hpair : termFreeBoundVec 2 (?[⌜v 0⌝,⌜v 1⌝] : V) = ?[termFreeBound (⌜v 0⌝ : V),termFreeBound (⌜v 1⌝ : V)] := by simpa [htail,one_add_one_eq_two] using hh
  rw [atomFreeBound,hpair,termFreeBound_quote,termFreeBound_quote,finFreeBound_union,natCast_max]
  simp

theorem relFreeVariables_two {n : Nat} (v : Fin 2 → SourceTerm n) :
    (Semiformula.rel PA194PAeq.Rel.eq v).freeVariables = (v 0).freeVariables ∪ (v 1).freeVariables := by
  ext x; simp [Semiformula.freeVariables_rel,Fin.exists_fin_two]
theorem nrelFreeVariables_two {n : Nat} (v : Fin 2 → SourceTerm n) :
    (Semiformula.nrel PA194PAeq.Rel.eq v).freeVariables = (v 0).freeVariables ∪ (v 1).freeVariables := by
  ext x; simp [Semiformula.freeVariables_nrel,Fin.exists_fin_two]

theorem formulaFreeBound_quote {n : Nat} (p : Semiproposition PA194PAeq.language n) :
    formulaFreeBound (⌜p⌝ : V) = (finFreeBound p.freeVariables : V) := by
  induction p using Semiformula.rec' with
  | hverum => simp [Semiformula.quote_verum,formulaFreeBound_verum,Semiformula.freeVariables_verum]
  | hfalsum => simp [Semiformula.quote_falsum,formulaFreeBound_falsum,Semiformula.freeVariables_falsum]
  | hrel r v =>
    have ht := (Semiformula.quote_isSemiformula (Semiformula.rel r v) : IsSemiformula PA194PAeq.language (_ : V) _).isUFormula
    rw [Semiformula.quote_rel] at ht
    have hr := (IsUFormula.rel.mp ht).1
    have hv := (IsUFormula.rel.mp ht).2
    cases r
    rw [Semiformula.quote_rel,formulaFreeBound_rel hr hv]
    simp only [Nat.cast_ofNat]
    rw [atomFreeBound_quoteVec,relFreeVariables_two]
  | hnrel r v =>
    have ht := (Semiformula.quote_isSemiformula (Semiformula.nrel r v) : IsSemiformula PA194PAeq.language (_ : V) _).isUFormula
    rw [Semiformula.quote_nrel] at ht
    have hr := (IsUFormula.nrel.mp ht).1
    have hv := (IsUFormula.nrel.mp ht).2
    cases r
    rw [Semiformula.quote_nrel,formulaFreeBound_nrel hr hv]
    simp only [Nat.cast_ofNat]
    rw [atomFreeBound_quoteVec,nrelFreeVariables_two]
  | hand a b iha ihb =>
    rw [Semiformula.quote_and,formulaFreeBound_and (Semiformula.quote_isSemiformula a).isUFormula (Semiformula.quote_isSemiformula b).isUFormula,
      iha,ihb,Semiformula.freeVariables_and,finFreeBound_union,natCast_max]
  | hor a b iha ihb =>
    rw [Semiformula.quote_or,formulaFreeBound_or (Semiformula.quote_isSemiformula a).isUFormula (Semiformula.quote_isSemiformula b).isUFormula,
      iha,ihb,Semiformula.freeVariables_or,finFreeBound_union,natCast_max]
  | hall a ih =>
    rw [Semiformula.quote_all,formulaFreeBound_all (Semiformula.quote_isSemiformula a).isUFormula,ih,Semiformula.freeVariables_all]
  | hexs a ih =>
    rw [Semiformula.quote_ex,formulaFreeBound_exs (Semiformula.quote_isSemiformula a).isUFormula,ih,Semiformula.freeVariables_exs]

theorem formulaFreeBound_quote_fvSup {n : Nat} (p : Semiproposition PA194PAeq.language n) :
    formulaFreeBound (⌜p⌝ : V) = (p.fvSup : V) := by
  simpa only [Semiformula.fvSup,finFreeBound] using formulaFreeBound_quote (V := V) p
#print axioms atomFreeBound_quoteVec
#print axioms formulaFreeBound_quote_fvSup
end generic
end PA194PAeqBind
