import PA194TypedSchema
import PA194FullSepTheoryModel
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194TypedClass
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.PA.RelationalSource
open PA194TypedSchema
open PA194TypedBound
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
local instance typedClassZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance typedClassOne : One M := ⟨F oneCode Fin.elim0⟩
local instance typedClassAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance typedClassMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance typedClassLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance typedClassIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A typed characterization whenever every internal arity-one code has a typed quote. -/
theorem fullSepUniform_typed_of_surjective (q : M)
    (hsurj : ∀ x : M, IsSemiformula SourceL 1 x →
      ∃ p : Semiproposition SourceL 1, (⌜p⌝ : M) = x) :
    (M ⊧/![q] fullSepUniform.val) ↔
      ∃ p : Semiproposition SourceL 1, (⌜(separationFormula p).univCl⌝ : M) = q := by
  rw [fullSepUniform_model]
  constructor
  · rintro ⟨x,hx,he⟩
    obtain ⟨p,rfl⟩ := hsurj x hx
    exact ⟨p,(fullyClosedSeparation_quote p).symm.trans he⟩
  · rintro ⟨p,hq⟩
    exact ⟨⌜p⌝,Semiformula.quote_isSemiformul₁ p,(fullyClosedSeparation_quote p).trans hq⟩

#print axioms fullSepUniform_typed_of_surjective
end models
end PA194TypedClass
