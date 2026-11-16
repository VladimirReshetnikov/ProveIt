import PA194TypedFix
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194TypedClosure
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.PA.RelationalSource
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
local instance typedClosureZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance typedClosureOne : One M := ⟨F oneCode Fin.elim0⟩
local instance typedClosureAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance typedClosureMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance typedClosureLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance typedClosureIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def typedCloseOne (p : Proposition M6.PA.RelationalSource.language) : Proposition M6.PA.RelationalSource.language :=
  ∀⁰ (Rew.fix ▹ p)

def typedCloseIter : Nat → Proposition M6.PA.RelationalSource.language → Proposition M6.PA.RelationalSource.language
  | 0, p => p
  | n+1, p => typedCloseOne (typedCloseIter n p)

theorem modelClose_quote (n : Nat) (p : Proposition M6.PA.RelationalSource.language) :
    modelClose (n : M) (⌜p⌝ : M) = (⌜typedCloseIter n p⌝ : M) := by
  induction n with
  | zero => simp [modelClose_zero,typedCloseIter]
  | succ n ih =>
    rw [Nat.cast_succ,modelClose_succ,ih]
    change ^∀ (bindFormula (0 : M) (⌜typedCloseIter n p⌝ : M)) = _
    have hfix := bindFormula_quote_fix (M := M) (n := 0) (typedCloseIter n p)
    simp only [Nat.cast_zero] at hfix
    rw [hfix]
    rfl

theorem typedCloseIter_eq_fixitr (n : Nat) (p : Proposition M6.PA.RelationalSource.language) :
    typedCloseIter n p = (∀⁰* (Rew.fixitr 0 n ▹ p)) := by
  induction n with
  | zero => simp [typedCloseIter]
  | succ n ih =>
    rw [LawfulSyntacticRewriting.allClosure_fixitr]
    simpa [typedCloseIter,typedCloseOne,ih]

theorem modelClose_quote_univCl (p : Proposition M6.PA.RelationalSource.language) :
    modelClose (p.fvSup : M) (⌜p⌝ : M) = (⌜p.univCl⌝ : M) := by
  rw [modelClose_quote,typedCloseIter_eq_fixitr]
  exact (quote_univCl (V := M) p).symm

#print axioms modelClose_quote
#print axioms typedCloseIter_eq_fixitr
#print axioms modelClose_quote_univCl
end models
end PA194TypedClosure
