import PA194Site31TransferClockCode
import PA194Site31CodedFrame
import PA194Site32CodedPositive
import PA194Site31PhysicalClock
import PA194SourceSite32PositivePhysical
import PA194SourceSite33Physical
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceSite31FullyCoded
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194Site31SentenceClock PA194SourceSite31Controller PA194SourceSite31Physical PA194SourceControllerCode TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PRAModelIOpenPairing PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem oneLoop (e : Fin 14 → M) (m : M)
    (hgap : PA194Site31TransferClockCode.env13 e 10 = e 13+1)
    (hm : PA194Site31TransferClockCode.env13 e 6 = m+1) :
    let prior := PA194Site31TransferClockCode.env13 e
    let args := PA194Site31SentenceClock.args prior
    let first := PA194Site31OutputFile.updated args (prior 11)
    let output := Function.update first 6 m
    F step ![F step ![F step ![sourceState 31 args (prior 9)]]] = sourceState 31 output (prior 9) ∧
    F PA194Stepper.stepper ![F PA194Site31TransferClockCode.clockCode e,
      physicalFrame 31 (((e 13+1)+1)+1) args] =
        physicalFrame 31 ((((e 13+1)+1)+1)+1) output := by
  dsimp only
  have h := PA194SourceSite31CodedLoop.oneLoop (PA194Site31TransferClockCode.env13 e) (e 13) m hgap hm
  dsimp only at h
  rw [PA194Site31TransferClockCode.modelClock]
  exact h
#print axioms oneLoop
end models
end PA194SourceSite31FullyCoded
