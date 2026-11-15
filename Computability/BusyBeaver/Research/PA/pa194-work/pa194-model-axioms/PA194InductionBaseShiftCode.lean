import PA194InternalInductionBaseShift
import PA194FixedSyntaxQuote
import PA194InternalOrdinalBase
import PA194BoundSeparation
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194InductionBaseShiftCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194InternalInductionBaseShift PA194FixedSyntaxQuote PA194InternalOrdinalBase PA194OrdinalFixed PA194OrdinalBaseQuote
  PA194TypedSeparation
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance boundSepZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance boundSepOne : One M := ⟨F oneCode Fin.elim0⟩
local instance boundSepAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance boundSepMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance boundSepLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance boundSepIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def baseCode (p : M) : M :=
  inductionBaseCode (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M) (⌜zeroTemplate⌝ : M) p

noncomputable def shiftBaseProofCode (p d : M) : M :=
  shiftRule ({baseCode (shift SourceL p)} : M) d

noncomputable def shiftBaseProofGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out p d. ∃ dt, !(fixedFormulaQuoteGraph PA194OrdinalBaseQuote.domainTemplate) dt ∧
    ∃ z, !(fixedFormulaQuoteGraph zeroTemplate) z ∧ ∃ t, !(shiftGraph SourceL) t p ∧
    ∃ b, !inductionBaseGraph b dt z t ∧ ∃ s, !expDef s b ∧ !shiftRuleGraph out s d”

theorem shiftBaseProofGraph_defined :
    𝚺₁-Function₂ (shiftBaseProofCode : M → M → M) via shiftBaseProofGraph := by
  haveI := inductionBaseGraph_defined (M := M)
  refine .mk fun v => ?_
  simp [shiftBaseProofGraph, shiftBaseProofCode, baseCode, fixedFormulaQuoteGraph_correct, singleton_def]

noncomputable def shiftBaseProofDirect (T : InternalTheory M SourceL) (p : M)
    (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢! (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL)) :
    T ⊢! (⟨baseCode (shift SourceL p), inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp.shift⟩ : Formula M SourceL) := by
  have he : setShift SourceL ({baseCode p} : M) = ({baseCode (shift SourceL p)} : M) := by
    apply mem_ext
    intro x
    simp [mem_setShift_iff, baseCode, baseTemplate_shift p hp]
  have dd : DerivationOf T.theory d.val ({baseCode p} : M) := by
    simpa [← singleton_eq_insert] using d.derivationOf
  have hd : Derivation T.theory (shiftRule (setShift SourceL ({baseCode p} : M)) d.val) :=
    Derivation.shiftRule dd
  refine ⟨shiftBaseProofCode p d.val, ?_⟩
  constructor
  · simp [shiftBaseProofCode]
  · simpa [shiftBaseProofCode, he] using hd

@[simp] theorem shiftBaseProofDirect_val (T : InternalTheory M SourceL) (p : M)
    (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢! (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL)) :
    (shiftBaseProofDirect T p hp d).val = shiftBaseProofCode p d.val := rfl

#print axioms shiftBaseProofGraph_defined
#print axioms shiftBaseProofDirect
#print axioms shiftBaseProofDirect_val
end models
end PA194InductionBaseShiftCode
