import PA194OrdinalFixed
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194FixedSyntaxQuote
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.PA.RelationalSource
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
local instance fixedSyntaxZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance fixedSyntaxOne : One M := ⟨F oneCode Fin.elim0⟩
local instance fixedSyntaxAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance fixedSyntaxMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance fixedSyntaxLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance fixedSyntaxIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Closed arithmetic graph for the code of a typed source term. -/
def fixedTermQuoteGraph : {n : Nat} → SyntacticSemiterm M6.PA.RelationalSource.language n → 𝚺₁.Semisentence 1
  | _, .bvar i => .mkSigma “q. !qqBvarDef q ↑(i.val)”
  | _, .fvar index => .mkSigma “q. !qqFvarDef q ↑index”
  | _, .func f _ => nomatch f

theorem fixedTermQuoteGraph_correct {n : Nat} (t : SyntacticSemiterm M6.PA.RelationalSource.language n) (q : M) :
    (fixedTermQuoteGraph t).val.Eval ![q] Empty.elim ↔ q = (⌜t⌝ : M) := by
  cases t with
  | bvar i => simp [fixedTermQuoteGraph,Semiterm.quote_bvar,numeral_eq_natCast]
  | fvar x => simp [fixedTermQuoteGraph,Semiterm.quote_fvar,numeral_eq_natCast]
  | func f v => nomatch f

theorem fixedTermQuoteGraph_correct_const {n : Nat} (t : SyntacticSemiterm M6.PA.RelationalSource.language n) (q : M) :
    (fixedTermQuoteGraph t).val.Eval (fun _ : Fin 1 => q) Empty.elim ↔ q = (⌜t⌝ : M) := by
  simpa only [Matrix.constant_eq_singleton] using fixedTermQuoteGraph_correct t q

/-- Closed arithmetic graph for the code of a typed relational-source formula. -/
noncomputable def fixedFormulaQuoteGraph : {n : Nat} → Semiproposition M6.PA.RelationalSource.language n → 𝚺₁.Semisentence 1
  | _, .verum => .mkSigma “q. !qqVerumDef q”
  | _, .falsum => .mkSigma “q. !qqFalsumDef q”
  | _, .rel .eq v => .mkSigma “q. ∃ a, !(fixedTermQuoteGraph (v 0)) a ∧ ∃ b, !(fixedTermQuoteGraph (v 1)) b ∧
      ∃ t, !adjoinDef t b 0 ∧ ∃ w, !adjoinDef w a t ∧ !qqRelDef q 2 0 w”
  | _, .rel .mem v => .mkSigma “q. ∃ a, !(fixedTermQuoteGraph (v 0)) a ∧ ∃ b, !(fixedTermQuoteGraph (v 1)) b ∧
      ∃ t, !adjoinDef t b 0 ∧ ∃ w, !adjoinDef w a t ∧ !qqRelDef q 2 1 w”
  | _, .nrel .eq v => .mkSigma “q. ∃ a, !(fixedTermQuoteGraph (v 0)) a ∧ ∃ b, !(fixedTermQuoteGraph (v 1)) b ∧
      ∃ t, !adjoinDef t b 0 ∧ ∃ w, !adjoinDef w a t ∧ !qqNRelDef q 2 0 w”
  | _, .nrel .mem v => .mkSigma “q. ∃ a, !(fixedTermQuoteGraph (v 0)) a ∧ ∃ b, !(fixedTermQuoteGraph (v 1)) b ∧
      ∃ t, !adjoinDef t b 0 ∧ ∃ w, !adjoinDef w a t ∧ !qqNRelDef q 2 1 w”
  | _, .and a b => .mkSigma “q. ∃ x, !(fixedFormulaQuoteGraph a) x ∧ ∃ y, !(fixedFormulaQuoteGraph b) y ∧ !qqAndDef q x y”
  | _, .or a b => .mkSigma “q. ∃ x, !(fixedFormulaQuoteGraph a) x ∧ ∃ y, !(fixedFormulaQuoteGraph b) y ∧ !qqOrDef q x y”
  | _, .all a => .mkSigma “q. ∃ x, !(fixedFormulaQuoteGraph a) x ∧ !qqAllDef q x”
  | _, .exs a => .mkSigma “q. ∃ x, !(fixedFormulaQuoteGraph a) x ∧ !qqExsDef q x”

theorem fixedFormulaQuoteGraph_correct {n : Nat} (p : Semiproposition M6.PA.RelationalSource.language n) :
    ∀ q : M, (fixedFormulaQuoteGraph p).val.Eval ![q] Empty.elim ↔ q = (⌜p⌝ : M) := by
  letI : GödelQuote (M6.PA.RelationalSource.language.Rel 2) M := gödelQuoteRel (L := M6.PA.RelationalSource.language) (V := M) 2
  have heq : (@GödelQuote.quote _ _ (gödelQuoteRel (L := M6.PA.RelationalSource.language) (V := M) 2) Relation.eq) = 0 := by
    change ((0 : Nat) : M) = 0
    simp
  have hmem : (@GödelQuote.quote _ _ (gödelQuoteRel (L := M6.PA.RelationalSource.language) (V := M) 2) Relation.mem) = 1 := by
    change ((1 : Nat) : M) = 1
    simp
  induction p using Semiformula.rec' with
  | hverum => intro q; simp [fixedFormulaQuoteGraph,Semiformula.quote_verum]
  | hfalsum => intro q; simp [fixedFormulaQuoteGraph,Semiformula.quote_falsum]
  | hrel r v =>
    cases r <;> intro q <;>
      simp [fixedFormulaQuoteGraph,fixedTermQuoteGraph_correct_const,Matrix.empty_eq,heq,hmem,Semiformula.quote_rel,
        SemitermVec.val_succ,Semiterm.quote_def,Matrix.vecHead,Matrix.vecTail,Function.comp_def,adjoin_def]
  | hnrel r v =>
    cases r <;> intro q <;>
      simp [fixedFormulaQuoteGraph,fixedTermQuoteGraph_correct_const,Matrix.empty_eq,heq,hmem,Semiformula.quote_nrel,
        SemitermVec.val_succ,Semiterm.quote_def,Matrix.vecHead,Matrix.vecTail,Function.comp_def,adjoin_def]
  | hand a b iha ihb => intro q; simp [fixedFormulaQuoteGraph,iha,ihb,Semiformula.quote_and]
  | hor a b iha ihb => intro q; simp [fixedFormulaQuoteGraph,iha,ihb,Semiformula.quote_or]
  | hall a ih => intro q; simp [fixedFormulaQuoteGraph,ih,Semiformula.quote_all]
  | hexs a ih => intro q; simp [fixedFormulaQuoteGraph,ih,Semiformula.quote_ex]

#print axioms fixedFormulaQuoteGraph_correct
#print axioms fixedFormulaQuoteGraph
#print axioms fixedTermQuoteGraph_correct
end models
end PA194FixedSyntaxQuote
