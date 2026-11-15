import PA194InternalInductionBaseShift
import PA194OrdinalFixed
import PA194InternalOrdinalBase
import PA194BoundSeparation
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194InternalInductionStepShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194InternalInductionBaseShift PA194InternalOrdinalBase PA194OrdinalFixed PA194OrdinalBaseQuote
  PA194InternalOrdinalStep PA194OrdinalStepFromProperty PA194OrdinalStepQuote
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

theorem shift_inductionStepCode (d₁ d₀ s p₁ p₀ : M)
    (hd₁ : IsSemiformula SourceL 2 d₁) (hd₀ : IsSemiformula SourceL 2 d₀)
    (hs : IsSemiformula SourceL 2 s) (hp₁ : IsSemiformula SourceL 2 p₁)
    (hp₀ : IsSemiformula SourceL 2 p₀) :
    shift SourceL (inductionStepCode d₁ d₀ s p₁ p₀) =
      inductionStepCode (shift SourceL d₁) (shift SourceL d₀) (shift SourceL s)
        (shift SourceL p₁) (shift SourceL p₀) := by
  have hsp : IsSemiformula SourceL 2 (s ^⋏ p₁) := by simp [IsSemiformula.and, hs, hp₁]
  have hdsp : IsSemiformula SourceL 2 (d₀ ^⋏ (s ^⋏ p₁)) := by simp [IsSemiformula.and, hd₀, hsp]
  have hall : IsSemiformula SourceL 2 (d₁ ^⋏ (d₀ ^⋏ (s ^⋏ p₁))) := by simp [IsSemiformula.and, hd₁, hdsp]
  have hor : IsUFormula SourceL (neg SourceL (d₁ ^⋏ (d₀ ^⋏ (s ^⋏ p₁))) ^⋎ p₀) :=
    (IsSemiformula.or.mpr ⟨hall.neg,hp₀⟩).isUFormula
  unfold inductionStepCode
  rw [shift_all (IsUFormula.all.mpr hor), shift_all hor,
    shift_or hall.neg.isUFormula hp₀.isUFormula, shift_neg hall,
    shift_and hd₁.isUFormula hdsp.isUFormula, shift_and hd₀.isUFormula hsp.isUFormula,
    shift_and hs.isUFormula hp₁.isUFormula]

theorem shift_propertyOne (p : M) (hp : IsSemiformula SourceL 1 p) :
    shift SourceL (substs1 SourceL (^#(1 : M)) p) =
      substs1 SourceL (^#(1 : M)) (shift SourceL p) := by
  unfold substs1
  rw [shift_substs hp (by simp : IsSemitermVec SourceL 1 2 (?[ ^#(1 : M)] : M))]
  simp

theorem stepTemplate_shift (p : M) (hp : IsSemiformula SourceL 1 p) :
    shift SourceL (ordinalStepFromProperty (⌜domainOne⌝ : M) (⌜domainZero⌝ : M) (⌜successorTemplate⌝ : M) p) =
    ordinalStepFromProperty (⌜domainOne⌝ : M) (⌜domainZero⌝ : M) (⌜successorTemplate⌝ : M) (shift SourceL p) := by
  have h1 : IsSemiformula SourceL 2 (substs1 SourceL (^#(1 : M)) p) := IsSemiformula.substs1 (by simp) hp
  have h0 : IsSemiformula SourceL 2 p := ⟨hp.isUFormula, le_trans hp.bv_le (by norm_num)⟩
  have hd₁ : IsSemiformula SourceL 2 (⌜domainOne⌝ : M) := by simpa using Semiformula.quote_isSemiformula domainOne
  have hd₀ : IsSemiformula SourceL 2 (⌜domainZero⌝ : M) := by simpa using Semiformula.quote_isSemiformula domainZero
  have hs : IsSemiformula SourceL 2 (⌜successorTemplate⌝ : M) := by simpa using Semiformula.quote_isSemiformula successorTemplate
  unfold ordinalStepFromProperty
  rw [shift_inductionStepCode _ _ _ _ _ hd₁ hd₀ hs h1 h0, shift_propertyOne p hp]
  rw [typed_quote_shift_fixed _ (by decide), typed_quote_shift_fixed _ (by decide), typed_quote_shift_fixed _ (by decide)]

#print axioms shift_inductionStepCode
#print axioms shift_propertyOne
#print axioms stepTemplate_shift
end models
end PA194InternalInductionStepShift
