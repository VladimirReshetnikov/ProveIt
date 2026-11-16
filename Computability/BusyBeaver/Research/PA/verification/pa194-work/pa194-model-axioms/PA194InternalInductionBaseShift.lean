import PA194OrdinalFixed
import PA194InternalOrdinalBase
import PA194BoundSeparation
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194InternalInductionBaseShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194InternalOrdinalBase PA194OrdinalFixed PA194OrdinalBaseQuote
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

theorem shift_inductionBaseCode (d z p : M)
    (hd : IsSemiformula SourceL 1 d) (hz : IsSemiformula SourceL 1 z)
    (hp : IsSemiformula SourceL 1 p) :
    shift SourceL (inductionBaseCode d z p) =
      inductionBaseCode (shift SourceL d) (shift SourceL z) (shift SourceL p) := by
  have hdz : IsSemiformula SourceL 1 (d ^⋏ z) := by simp [IsSemiformula.and, hd, hz]
  have hn : IsUFormula SourceL (neg SourceL (d ^⋏ z)) := hdz.isUFormula.neg
  unfold inductionBaseCode
  rw [shift_all ((IsSemiformula.or.mpr ⟨hdz.neg,hp⟩).isUFormula),
    shift_or hn hp.isUFormula, shift_neg hdz, shift_and hd.isUFormula hz.isUFormula]

theorem typed_quote_shift_fixed {n : Nat} (p : Semiproposition M6.PA.RelationalSource.language n)
    (hp : p.freeVariables = ∅) : shift SourceL (⌜p⌝ : M) = (⌜p⌝ : M) := by
  rw [← Semiformula.quote_shift]
  have h : Rewriting.shift p = p := by
    apply Semiformula.rew_eq_self_of
    · intro x; simp [Rewriting.shift]
    · intro x hx
      have hm : x ∈ p.freeVariables := hx
      simp [hp] at hm
  rw [h]

theorem baseTemplate_shift (p : M) (hp : IsSemiformula SourceL 1 p) :
    shift SourceL (inductionBaseCode (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M) (⌜zeroTemplate⌝ : M) p) =
    inductionBaseCode (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M) (⌜zeroTemplate⌝ : M) (shift SourceL p) := by
  rw [shift_inductionBaseCode _ _ _ (Semiformula.quote_isSemiformul₁ _) (Semiformula.quote_isSemiformul₁ _) hp]
  rw [typed_quote_shift_fixed _ (by decide), typed_quote_shift_fixed _ (by decide)]

#print axioms baseTemplate_shift
#print axioms typed_quote_shift_fixed
#print axioms shift_inductionBaseCode
end models
end PA194InternalInductionBaseShift
