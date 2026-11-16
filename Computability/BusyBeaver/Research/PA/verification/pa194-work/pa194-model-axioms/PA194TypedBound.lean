import PA194TypedClosure
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194TypedBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.PA.RelationalSource
open PA194TypedClosure
open PA194TypedFix
open PA194TypedSeparation
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
local instance typedBoundZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance typedBoundOne : One M := ⟨F oneCode Fin.elim0⟩
local instance typedBoundAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance typedBoundMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance typedBoundLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance typedBoundIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def finFreeBound (s : Finset Nat) : Nat := (s.max).recBotCoe 0 Nat.succ

@[simp] theorem finFreeBound_empty : finFreeBound ∅ = 0 := by simp [finFreeBound]
@[simp] theorem finFreeBound_singleton (x : Nat) : finFreeBound {x} = x+1 := by simp [finFreeBound]
theorem finFreeBound_union (s t : Finset Nat) : finFreeBound (s ∪ t) = max (finFreeBound s) (finFreeBound t) := by
  unfold finFreeBound
  rw [Finset.max_union]
  generalize hs : s.max = a
  generalize ht : t.max = b
  cases a using WithBot.recBotCoe with
  | bot => simp
  | coe a =>
    cases b using WithBot.recBotCoe with
    | bot => simp
    | coe b =>
      rw [← WithBot.coe_max]
      simp only [WithBot.recBotCoe_coe, Nat.succ_max_succ]

theorem termFreeBound_quote {n : Nat} (t : SyntacticSemiterm M6.PA.RelationalSource.language n) :
    termFreeBound (⌜t⌝ : M) = (finFreeBound t.freeVariables : M) := by
  cases t with
  | bvar x => simp [termFreeBound_bvar,Semiterm.freeVariables_bvar]
  | fvar x => simp [termFreeBound_fvar,Semiterm.freeVariables_fvar]
  | func f v => nomatch f

theorem natCast_max (a b : Nat) : ((max a b : Nat) : M) = max (a : M) (b : M) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by exact_mod_cast h)]
  · rw [max_eq_left h, max_eq_left (by exact_mod_cast h)]

theorem pairFreeBound_quoteVec {n : Nat} (v : Fin 2 → SyntacticSemiterm M6.PA.RelationalSource.language n) :
    pairFreeBound (SemitermVec.val fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm M M6.PA.RelationalSource.language n)) =
      (finFreeBound ((v 0).freeVariables ∪ (v 1).freeVariables) : M) := by
  have hvec : SemitermVec.val (fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm M M6.PA.RelationalSource.language n)) =
      (?[ (⌜v 0⌝ : M), (⌜v 1⌝ : M)] : M) := by
    simp [SemitermVec.val_succ,Semiterm.quote_def,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  rw [hvec,pairFreeBound_pair,termFreeBound_quote,termFreeBound_quote,finFreeBound_union,natCast_max]

theorem relFreeVariables_two {n : Nat} (r : Relation 2)
    (v : Fin 2 → SyntacticSemiterm M6.PA.RelationalSource.language n) :
    (Semiformula.rel r v).freeVariables = (v 0).freeVariables ∪ (v 1).freeVariables := by
  ext x
  simp [Semiformula.freeVariables_rel,Fin.exists_fin_two]

theorem nrelFreeVariables_two {n : Nat} (r : Relation 2)
    (v : Fin 2 → SyntacticSemiterm M6.PA.RelationalSource.language n) :
    (Semiformula.nrel r v).freeVariables = (v 0).freeVariables ∪ (v 1).freeVariables := by
  ext x
  simp [Semiformula.freeVariables_nrel,Fin.exists_fin_two]

theorem formulaFreeBound_quote {n : Nat} (p : Semiproposition M6.PA.RelationalSource.language n) :
    formulaFreeBound (⌜p⌝ : M) = (finFreeBound p.freeVariables : M) := by
  induction p using Semiformula.rec' with
  | hverum => simp [Semiformula.quote_verum,formulaFreeBound_verum,Semiformula.freeVariables_verum]
  | hfalsum => simp [Semiformula.quote_falsum,formulaFreeBound_falsum,Semiformula.freeVariables_falsum]
  | hrel r v =>
    have ht := (Semiformula.quote_isSemiformula (Semiformula.rel r v) : IsSemiformula SourceL (_ : M) _).isUFormula
    rw [Semiformula.quote_rel] at ht
    have hr := (IsUFormula.rel.mp ht).1
    have hv := (IsUFormula.rel.mp ht).2
    cases r <;> rw [Semiformula.quote_rel,formulaFreeBound_rel _ _ _ hr hv,pairFreeBound_quoteVec,relFreeVariables_two]
  | hnrel r v =>
    have ht := (Semiformula.quote_isSemiformula (Semiformula.nrel r v) : IsSemiformula SourceL (_ : M) _).isUFormula
    rw [Semiformula.quote_nrel] at ht
    have hr := (IsUFormula.nrel.mp ht).1
    have hv := (IsUFormula.nrel.mp ht).2
    cases r <;> rw [Semiformula.quote_nrel,formulaFreeBound_nrel _ _ _ hr hv,pairFreeBound_quoteVec,nrelFreeVariables_two]
  | hand a b iha ihb =>
    rw [Semiformula.quote_and, formulaFreeBound_and _ _ (Semiformula.quote_isSemiformula a).isUFormula (Semiformula.quote_isSemiformula b).isUFormula,
      iha,ihb,Semiformula.freeVariables_and,finFreeBound_union,natCast_max]
  | hor a b iha ihb =>
    rw [Semiformula.quote_or, formulaFreeBound_or _ _ (Semiformula.quote_isSemiformula a).isUFormula (Semiformula.quote_isSemiformula b).isUFormula,
      iha,ihb,Semiformula.freeVariables_or,finFreeBound_union,natCast_max]
  | hall a ih =>
    rw [Semiformula.quote_all,formulaFreeBound_all _ (Semiformula.quote_isSemiformula a).isUFormula,ih,Semiformula.freeVariables_all]
  | hexs a ih =>
    rw [Semiformula.quote_ex,formulaFreeBound_ex _ (Semiformula.quote_isSemiformula a).isUFormula,ih,Semiformula.freeVariables_exs]

theorem formulaFreeBound_quote_fvSup {n : Nat} (p : Semiproposition M6.PA.RelationalSource.language n) :
    formulaFreeBound (⌜p⌝ : M) = (p.fvSup : M) := by
  simpa only [Semiformula.fvSup,finFreeBound] using formulaFreeBound_quote (M := M) p

#print axioms formulaFreeBound_quote
#print axioms formulaFreeBound_quote_fvSup
#print axioms pairFreeBound_quoteVec
#print axioms relFreeVariables_two
#print axioms termFreeBound_quote
#print axioms natCast_max
#print axioms finFreeBound_union
end models
end PA194TypedBound
