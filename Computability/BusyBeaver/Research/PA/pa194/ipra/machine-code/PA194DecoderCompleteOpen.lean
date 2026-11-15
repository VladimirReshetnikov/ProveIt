import PA194DecoderClockOpen
import PA194UnpairExit
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194DecoderCompleteOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASubAddition
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive
open PA194IteratedSimulation PA194DecoderSynchronizationOpen PA194DecoderClock PA194UnpairExit
open PA194DiagonalIteration PA194DiagonalLink PA194MachineProjections PA194TargetCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem decode (initial : Fin 11 → M) (tail : M) :
    let start := sourceState 34 initial tail
    let p := cantor (initial 6) (initial 7)+initial 8
    F PA194SourceControllerCode.run ![F totalClock ![initial 8,start]+1,start] =
      sourceState 42 (argsAt initial (F fixedFirst ![p]) (F fixedSecond ![p]) 0) tail := by
  let start := sourceState 34 initial tail
  let p := cantor (initial 6) (initial 7)+initial 8
  let seed := pair (initial 6) (initial 7)
  let d := F PA194DiagonalCode.run ![initial 8,seed]
  have hzero : F subCode ![initial 8,initial 8] = (0 : M) := by
    have h := modelSubAdd (initial 8) (0 : M)
    change F subCode ![initial 8+0,initial 8] = (0 : M) at h
    simpa only [add_zero] using h
  have hsync := PA194DecoderSynchronizationOpen.synchronization initial tail (initial 8) (le_refl _)
  change F (iterate PA194DecoderRoundCode.advance) ![initial 8,start] =
    sourceState 34 (argsAt initial (pi₁ d) (pi₂ d) (F subCode ![initial 8,initial 8])) tail at hsync
  rw [hzero] at hsync
  have hclock := PA194DecoderClockOpen.accumulate start (initial 8)
  have hproj := iterationProjects seed (initial 8)
  change F fixedFirst ![F scoreCode ![seed]+initial 8] = pi₁ d ∧
    F fixedSecond ![F scoreCode ![seed]+initial 8] = pi₂ d at hproj
  rw [modelScore] at hproj
  have hscores : cantor (pi₁ seed) (pi₂ seed)+initial 8 = p := by simp [seed,p,pi₁_pair,pi₂_pair]
  rw [hscores] at hproj
  let out := argsAt initial (F fixedFirst ![p]) (F fixedSecond ![p]) (0 : M)
  have h8 : out 8 = (0 : M) := by simp [out,argsAt]
  have hexit := exitTo42 out tail h8
  change F (iterate step) ![F totalClock ![initial 8,start]+1,start] = sourceState 42 out tail
  rw [PA194DiagonalIteration.iterSucc]
  change F step ![F PA194SourceControllerCode.run ![F totalClock ![initial 8,start],start]] = _
  rw [hclock,hsync,←hproj.1,←hproj.2]
  exact hexit

theorem decodeCode (initial : Fin 11 → M) (tail : M) :
    let start := sourceState 34 initial tail
    let p := F addCode ![F fixedCantor ![initial 6,initial 7],initial 8]
    F PA194SourceControllerCode.run ![F totalClock ![initial 8,start]+1,start] =
      sourceState 42 (argsAt initial (F fixedFirst ![p]) (F fixedSecond ![p]) 0) tail := by
  have h := decode initial tail
  rw [modelCantorSelected fixedCantor fixedCantor_certified] 
  exact h
#print axioms decode
#print axioms decodeCode
end models
end PA194DecoderCompleteOpen
