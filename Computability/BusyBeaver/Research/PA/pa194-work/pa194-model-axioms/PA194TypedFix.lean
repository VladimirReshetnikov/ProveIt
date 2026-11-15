import PA194TypedSepQuote
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194TypedFix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.PA.RelationalSource
open PA194BindSource
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance typedFixZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance typedFixOne : One M := ⟨F oneCode Fin.elim0⟩
local instance typedFixAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance typedFixMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance typedFixLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance typedFixIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem bindTerm_quote_fix {n : Nat} (t : SyntacticSemiterm M6.PA.RelationalSource.language n) :
    bindTerm (n : M) (⌜t⌝ : M) = (⌜(Rew.fix t : SyntacticSemiterm M6.PA.RelationalSource.language (n+1))⌝ : M) := by
  cases t with
  | bvar x => simp [Rew.fix_bvar,bindTerm_bvar]
  | fvar x =>
    cases x with
    | zero => simp [Rew.fix_fvar_zero,bindTerm_fvar_zero]
    | succ x => simp [Rew.fix_fvar_succ,bindTerm_fvar_succ]
  | func f v => nomatch f

theorem bindPair_quote_fix {n : Nat} (v : Fin 2 → SyntacticSemiterm M6.PA.RelationalSource.language n) :
    bindPair (n : M) (SemitermVec.val fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm M M6.PA.RelationalSource.language n)) =
      SemitermVec.val (fun i ↦ (⌜(Rew.fix (v i) : SyntacticSemiterm M6.PA.RelationalSource.language (n+1))⌝ : Bootstrapping.Semiterm M M6.PA.RelationalSource.language (n+1))) := by
  have hvec : SemitermVec.val (fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm M M6.PA.RelationalSource.language n)) =
      (?[ (⌜v 0⌝ : M), (⌜v 1⌝ : M)] : M) := by
    simp [SemitermVec.val_succ,Semiterm.quote_def,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  have hvec' : SemitermVec.val (fun i ↦ (⌜(Rew.fix (v i) : SyntacticSemiterm M6.PA.RelationalSource.language (n+1))⌝ : Bootstrapping.Semiterm M M6.PA.RelationalSource.language (n+1))) =
      (?[ (⌜(Rew.fix (v 0) : SyntacticSemiterm M6.PA.RelationalSource.language (n+1))⌝ : M),
          (⌜(Rew.fix (v 1) : SyntacticSemiterm M6.PA.RelationalSource.language (n+1))⌝ : M)] : M) := by
    simp [SemitermVec.val_succ,Semiterm.quote_def,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  rw [hvec,hvec']
  have h1 : (?[ (⌜v 0⌝ : M), (⌜v 1⌝ : M)] : M).[1] = ⌜v 1⌝ := by
    have he : (1 : M) = (0 : M)+1 := by simp
    rw [he,nth_adjoin_succ,nth_adjoin_zero]
  simp only [bindPair,nth_adjoin_zero,h1,bindTerm_quote_fix]

theorem bindFormula_quote_fix {n : Nat} (p : Semiproposition M6.PA.RelationalSource.language n) :
    bindFormula (n : M) (⌜p⌝ : M) = (⌜(Rew.fix ▹ p : Semiproposition M6.PA.RelationalSource.language (n+1))⌝ : M) := by
  induction p using Semiformula.rec' with
  | hverum => simp [bindFormula_verum,Semiformula.quote_verum]
  | hfalsum => simp [bindFormula_falsum,Semiformula.quote_falsum]
  | hrel r v =>
    have ht := (Semiformula.quote_isSemiformula (Semiformula.rel r v) : IsSemiformula SourceL (_ : M) _).isUFormula
    rw [Semiformula.quote_rel] at ht
    have hr := (IsUFormula.rel.mp ht).1
    have hv := (IsUFormula.rel.mp ht).2
    cases r <;> simp only [Semiformula.rew_rel,Semiformula.quote_rel]
    all_goals rw [bindFormula_rel _ _ _ _ hr hv,bindPair_quote_fix]
  | hnrel r v =>
    have ht := (Semiformula.quote_isSemiformula (Semiformula.nrel r v) : IsSemiformula SourceL (_ : M) _).isUFormula
    rw [Semiformula.quote_nrel] at ht
    have hr := (IsUFormula.nrel.mp ht).1
    have hv := (IsUFormula.nrel.mp ht).2
    cases r <;> simp only [Semiformula.rew_nrel,Semiformula.quote_nrel]
    all_goals rw [bindFormula_nrel _ _ _ _ hr hv,bindPair_quote_fix]
  | hand a b iha ihb =>
    simp only [LogicalConnective.HomClass.map_and,Semiformula.quote_and]
    rw [bindFormula_and _ _ _ (Semiformula.quote_isSemiformula a).isUFormula (Semiformula.quote_isSemiformula b).isUFormula, iha,ihb]
  | hor a b iha ihb =>
    simp only [LogicalConnective.HomClass.map_or,Semiformula.quote_or]
    rw [bindFormula_or _ _ _ (Semiformula.quote_isSemiformula a).isUFormula (Semiformula.quote_isSemiformula b).isUFormula, iha,ihb]
  | hall a ih =>
    rw [Rewriting.app_all,Semiformula.quote_all,bindFormula_all _ _ (Semiformula.quote_isSemiformula a).isUFormula]
    rw [Rew.q_fix,Semiformula.quote_all]
    congr 1
  | hexs a ih =>
    rw [Rewriting.app_exs,Semiformula.quote_ex,bindFormula_ex _ _ (Semiformula.quote_isSemiformula a).isUFormula]
    rw [Rew.q_fix,Semiformula.quote_ex]
    congr 1

#print axioms bindFormula_quote_fix
#print axioms bindPair_quote_fix
#print axioms bindTerm_quote_fix
end models
end PA194TypedFix
