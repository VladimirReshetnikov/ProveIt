import PA194PhysicalLoopTo32
import PA194SourceSite31Controller
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194SourceLoopTo32
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopCost PA194ModelSourceLoop PA194ActualSourceLoop PA194ActualLoopOrbit PA194ControllerLoopFrame PA194OneSpareReturn PA194StateOne PA194ZeroRuns PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch PA194RegisterFile PA194RegisterPermutation PA194Path27Header
open PA194SourceControllerCode PA194SourceSite25Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem reaches32 (r : Fin 9 → M) (tail k n spare : M) :
    let r' := running r (r 0)
    let count := (n+r 0)+r 0
    let a' := frameArgs r' count spare
    F step ![F step ![F (iterCode quad) ![r 0,PA194ModelSourceLoop.source r tail]]] =
      PA194SourceSite31Controller.sourceState 32 (PA194Site31OutputFile.updated a' count) tail := by
  dsimp only
  let r' := running r (r 0)
  let count := (n+r 0)+r 0
  let a' := frameArgs r' count spare
  have hz0 : r' 0 = (0 : M) := by
    have h : F subCode ![r 0,r 0] = (0 : M) := by rw [modelSubAsTsub]; simp
    simpa [r',running] using h
  have hz : a' 0 = (0 : M) := by simpa [a',frameArgs,PA194ActualSourceLoop.args] using hz0
  have hit := PA194ActualSourceLoop.sourceIteration r tail (r 0) (le_refl (r 0))
  have hsrc := controllerSource r' count spare tail
  change sourceState 27 a' tail = PA194ModelSourceLoop.source r' tail at hsrc
  have hzero := (PA194SourceSite27Zero.zeroBranch ((k+1)+r 0) tail a' hz).1
  have hinc := PA194SourceSite31Controller.controllerStep a' tail (F repeatOutput ![F Code.succ (fun _ => count),(0 : M)])
  change F step ![sourceState 31 a' tail] =
    PA194SourceSite31Controller.sourceState 32 (PA194Site31OutputFile.updated a' count) tail at hinc
  rw [hit,←hsrc,hzero,hinc]
#print axioms reaches32
end models
end PA194SourceLoopTo32
