import PA194InternalInductionStepShift
import PA194FixedSyntaxQuote
import PA194InternalOrdinalBase
import PA194BoundSeparation
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194InductionStepShiftCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194InternalInductionStepShift PA194OrdinalStepFromProperty PA194OrdinalStepQuote PA194FixedSyntaxQuote PA194InternalOrdinalBase PA194OrdinalFixed PA194OrdinalBaseQuote
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

noncomputable def stepCode (p : M) : M :=
  ordinalStepFromProperty (⌜domainOne⌝ : M) (⌜domainZero⌝ : M) (⌜successorTemplate⌝ : M) p

theorem stepCode_scoped (p : M) (hp : IsSemiformula SourceL 1 p) : IsSemiformula SourceL 0 (stepCode p) := by
  apply ordinalStepFromProperty_scoped
  · simpa using (Semiformula.quote_isSemiformula domainOne : IsSemiformula SourceL ((2 : Nat) : M) _)
  · simpa using (Semiformula.quote_isSemiformula domainZero : IsSemiformula SourceL ((2 : Nat) : M) _)
  · simpa using (Semiformula.quote_isSemiformula successorTemplate : IsSemiformula SourceL ((2 : Nat) : M) _)
  · exact hp

noncomputable def shiftStepProofCode (p d : M) : M :=
  shiftRule ({stepCode (shift SourceL p)} : M) d

noncomputable def shiftStepProofGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out p d. ∃ d1, !(fixedFormulaQuoteGraph domainOne) d1 ∧
    ∃ d0, !(fixedFormulaQuoteGraph domainZero) d0 ∧ ∃ s, !(fixedFormulaQuoteGraph successorTemplate) s ∧
    ∃ t, !(shiftGraph SourceL) t p ∧ ∃ b, !ordinalStepFromPropertyGraph b d1 d0 s t ∧
    ∃ a, !expDef a b ∧ !shiftRuleGraph out a d”

theorem shiftStepProofGraph_defined :
    𝚺₁-Function₂ (shiftStepProofCode : M → M → M) via shiftStepProofGraph := by
  haveI := ordinalStepFromPropertyGraph_defined (M := M)
  refine .mk fun v => ?_
  simp [shiftStepProofGraph, shiftStepProofCode, stepCode, fixedFormulaQuoteGraph_correct, singleton_def]

noncomputable def shiftStepProofDirect (T : InternalTheory M SourceL) (p : M)
    (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢! (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL)) :
    T ⊢! (⟨stepCode (shift SourceL p), stepCode_scoped (shift SourceL p) hp.shift⟩ : Formula M SourceL) := by
  have he : setShift SourceL ({stepCode p} : M) = ({stepCode (shift SourceL p)} : M) := by
    apply mem_ext
    intro x
    simp [mem_setShift_iff, stepCode, stepTemplate_shift p hp]
  have dd : DerivationOf T.theory d.val ({stepCode p} : M) := by
    simpa [← singleton_eq_insert] using d.derivationOf
  have hd : Derivation T.theory (shiftRule (setShift SourceL ({stepCode p} : M)) d.val) :=
    Derivation.shiftRule dd
  refine ⟨shiftStepProofCode p d.val, ?_⟩
  constructor
  · simp [shiftStepProofCode]
  · simpa [shiftStepProofCode, he] using hd

@[simp] theorem shiftStepProofDirect_val (T : InternalTheory M SourceL) (p : M)
    (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢! (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL)) :
    (shiftStepProofDirect T p hp d).val = shiftStepProofCode p d.val := rfl

#print axioms stepCode_scoped
#print axioms shiftStepProofGraph_defined
#print axioms shiftStepProofDirect
#print axioms shiftStepProofDirect_val
end models
end PA194InductionStepShiftCode
