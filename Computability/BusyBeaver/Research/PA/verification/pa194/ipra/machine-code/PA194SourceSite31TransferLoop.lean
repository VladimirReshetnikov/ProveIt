import PA194Site31PhysicalClock
import PA194SourceSite32PositivePhysical
import PA194SourceSite33Physical
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceSite31TransferLoop
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194SourceSite31Controller PA194SourceSite31Physical PA194SourceControllerCode TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PRAModelIOpenPairing PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem oneLoop (k count tail m : M) (args : Fin 11 → M)
    (he : physicalArgs args 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)])
    (hm : args 6 = m+1) :
    let first := PA194Site31OutputFile.updated args count
    let output := Function.update first 6 m
    F step ![F step ![F step ![sourceState 31 args tail]]] = sourceState 31 output tail ∧
    ∃ clock : M,
      F PA194Stepper.stepper ![modelNumeral M 34,F PA194Stepper.stepper ![clock,
        PA194Site31AfterRun.runAfter (k+1) count args
          (F PA194Stepper.stepper ![PA194Site31PhysicalClock.clock24 (k+1) count args,
            physicalFrame 31 (((k+1)+1)+1) args])]] =
        physicalFrame 31 ((((k+1)+1)+1)+1) output := by
  dsimp only
  let first := PA194Site31OutputFile.updated args count
  let output := Function.update first 6 m
  have hm' : first 6 = m+1 := by simpa [first,PA194Site31OutputFile.updated] using hm
  have hs31 := PA194SourceSite31Controller.controllerStep args tail (F PA194OneSpareReturn.repeatOutput ![F Code.succ (fun _ => count),(0 : M)])
  change F step ![sourceState 31 args tail] = sourceState 32 first tail at hs31
  have hp31 := PA194Site31PhysicalClock.frameStep (k+1) count args he
  have h32 := PA194SourceSite32PositivePhysical.positiveBranch k tail m first hm'
  have h33 := PA194SourceSite33Physical.sourcePhysical (k+1) tail output
  obtain ⟨hs32,clock,hp32⟩ := h32
  obtain ⟨hs33,hp33⟩ := h33
  constructor
  · rw [hs31,hs32,hs33]
  · refine ⟨clock,?_⟩
    rw [hp31,hp32,hp33]
#print axioms oneLoop
end models
end PA194SourceSite31TransferLoop
