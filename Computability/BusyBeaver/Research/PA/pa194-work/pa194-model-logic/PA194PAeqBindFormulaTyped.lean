import PA194PAeqBindTyped
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ForwardTyped
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem bindTermVec_quote_fix {n : Nat} (v : Fin 2 → SourceTerm n) :
    bindTermVec (n : V) 2 (SemitermVec.val fun i => (⌜v i⌝ : Bootstrapping.Semiterm V PA194PAeq.language n)) =
      SemitermVec.val (fun i => (⌜(Rew.fix (v i) : SourceTerm (n+1))⌝ : Bootstrapping.Semiterm V PA194PAeq.language (n+1))) := by
  have hvec : SemitermVec.val (fun i => (⌜v i⌝ : Bootstrapping.Semiterm V PA194PAeq.language n)) =
      (?[ (⌜v 0⌝ : V), (⌜v 1⌝ : V)] : V) := by
    simp [SemitermVec.val_succ,Semiterm.quote_def,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  have hvec' : SemitermVec.val (fun i => (⌜(Rew.fix (v i) : SourceTerm (n+1))⌝ : Bootstrapping.Semiterm V PA194PAeq.language (n+1))) =
      (?[ (⌜(Rew.fix (v 0) : SourceTerm (n+1))⌝ : V), (⌜(Rew.fix (v 1) : SourceTerm (n+1))⌝ : V)] : V) := by
    simp [SemitermVec.val_succ,Semiterm.quote_def,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  rw [hvec,hvec']
  have h0 := quote_term_valid (V := V) (v 0)
  have h1 := quote_term_valid (V := V) (v 1)
  have hv1 : IsUTermVec PA194PAeq.language (1 : V) (?[⌜v 1⌝] : V) := by simp [h1]
  have hh := bindTermVec_cons (k := (n : V)) h0 hv1
  have hh' := bindTermVec_cons (k := (n : V)) h1 (show IsUTermVec PA194PAeq.language (0 : V) 0 by simp)
  have htail : bindTermVec (n : V) 1 (?[⌜v 1⌝] : V) = ?[bindTerm (n : V) ⌜v 1⌝] := by simpa using hh'
  have hpair : bindTermVec (n : V) 2 (?[⌜v 0⌝,⌜v 1⌝] : V) = ?[bindTerm (n : V) ⌜v 0⌝,bindTerm (n : V) ⌜v 1⌝] := by
    simpa [htail,one_add_one_eq_two] using hh
  rw [hpair,bindTerm_quote_fix,bindTerm_quote_fix]

theorem bindFormula_quote_fix {n : Nat} (p : Semiproposition PA194PAeq.language n) :
    bindFormula (n : V) (⌜p⌝ : V) = (⌜(Rew.fix ▹ p : Semiproposition PA194PAeq.language (n+1))⌝ : V) := by
  induction p using Semiformula.rec' with
  | hverum => simp [bindFormula_verum,Semiformula.quote_verum]
  | hfalsum => simp [bindFormula_falsum,Semiformula.quote_falsum]
  | hrel r v =>
    have ht := (Semiformula.quote_isSemiformula (Semiformula.rel r v) : IsSemiformula PA194PAeq.language (_ : V) _).isUFormula
    rw [Semiformula.quote_rel] at ht
    have hr := (IsUFormula.rel.mp ht).1
    have hv := (IsUFormula.rel.mp ht).2
    cases r <;> simp only [Semiformula.rew_rel,Semiformula.quote_rel]
    all_goals rw [bindFormula_rel hr hv]
    all_goals simp only [Nat.cast_ofNat]
    all_goals rw [bindTermVec_quote_fix]
  | hnrel r v =>
    have ht := (Semiformula.quote_isSemiformula (Semiformula.nrel r v) : IsSemiformula PA194PAeq.language (_ : V) _).isUFormula
    rw [Semiformula.quote_nrel] at ht
    have hr := (IsUFormula.nrel.mp ht).1
    have hv := (IsUFormula.nrel.mp ht).2
    cases r <;> simp only [Semiformula.rew_nrel,Semiformula.quote_nrel]
    all_goals rw [bindFormula_nrel hr hv]
    all_goals simp only [Nat.cast_ofNat]
    all_goals rw [bindTermVec_quote_fix]
  | hand a b iha ihb =>
    simp only [LogicalConnective.HomClass.map_and,Semiformula.quote_and]
    rw [bindFormula_and (Semiformula.quote_isSemiformula a).isUFormula (Semiformula.quote_isSemiformula b).isUFormula,iha,ihb]
  | hor a b iha ihb =>
    simp only [LogicalConnective.HomClass.map_or,Semiformula.quote_or]
    rw [bindFormula_or (Semiformula.quote_isSemiformula a).isUFormula (Semiformula.quote_isSemiformula b).isUFormula,iha,ihb]
  | hall a ih =>
    rw [Rewriting.app_all,Semiformula.quote_all,bindFormula_all (Semiformula.quote_isSemiformula a).isUFormula]
    rw [Rew.q_fix,Semiformula.quote_all]
    congr 1
  | hexs a ih =>
    rw [Rewriting.app_exs,Semiformula.quote_ex,bindFormula_exs (Semiformula.quote_isSemiformula a).isUFormula]
    rw [Rew.q_fix,Semiformula.quote_ex]
    congr 1
#print axioms bindTermVec_quote_fix
#print axioms bindFormula_quote_fix
end generic
end PA194PAeqBind
