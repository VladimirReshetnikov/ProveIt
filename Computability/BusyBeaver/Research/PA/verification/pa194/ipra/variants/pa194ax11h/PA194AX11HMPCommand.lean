import PA194AX11HFetchDecode
import PA194AX11HMPDispatch
import PA194AX11HMPSource
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194AX11HMPCommand
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194PausedReach
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem decoded (a : Fin 11 → M) (tail : M) (opcode : a 3 = 1) (hx : a 6 = 0) (hy : a 7 = 0) :
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 48 a tail)
      (sourceState 25 (PA194AX11HMPSource.output (Function.update a 3 0)) tail) := by
  let b := Function.update a 3 0
  have hx' : b 6 = 0 := by simpa [b] using hx
  have hy' : b 7 = 0 := by simpa [b] using hy
  exact PA194PausedReach.append _ (PA194AX11HMPDispatch.mp a tail opcode)
    (PA194AX11HMPSource.mp_source b tail hx' hy')

theorem fresh (a : Fin 11 → M) (tail : M) (h0 : a 8 = 0) (hx : a 6 = 0) (hy : a 7 = 0)
    (opcode : PA194AX11HFetchReader.output (PA194AX11HFetchDecode.freshFile a) 3 = 1) :
    let b := PA194AX11HFetchReader.output (PA194AX11HFetchDecode.freshFile a)
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 25 a tail)
      (sourceState 25 (PA194AX11HMPSource.output (Function.update b 3 0)) tail) := by
  dsimp only
  let b := PA194AX11HFetchReader.output (PA194AX11HFetchDecode.freshFile a)
  have hx' : b 6 = 0 := by simpa [b,PA194AX11HFetchReader.output,PA194AX11HFetchDecode.freshFile] using hx
  have hy' : b 7 = 0 := by simpa [b,PA194AX11HFetchReader.output,PA194AX11HFetchDecode.freshFile] using hy
  exact PA194PausedReach.append _ (PA194AX11HFetchDecode.fresh a tail h0 hx hy) (decoded b tail opcode hx' hy')

theorem positive (a : Fin 11 → M) (tail m : M) (h : a 8 = m+1) (hx : a 6 = 0) (hy : a 7 = 0)
    (opcode : PA194AX11HFetchReader.output (Function.update a 8 m) 3 = 1) :
    let b := PA194AX11HFetchReader.output (Function.update a 8 m)
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 25 a tail)
      (sourceState 25 (PA194AX11HMPSource.output (Function.update b 3 0)) tail) := by
  dsimp only
  let b := PA194AX11HFetchReader.output (Function.update a 8 m)
  have hx' : b 6 = 0 := by simpa [b,PA194AX11HFetchReader.output] using hx
  have hy' : b 7 = 0 := by simpa [b,PA194AX11HFetchReader.output] using hy
  exact PA194PausedReach.append _ (PA194AX11HFetchDecode.positive a tail m h hx hy) (decoded b tail opcode hx' hy')
#print axioms decoded
#print axioms fresh
#print axioms positive
end models
end PA194AX11HMPCommand
