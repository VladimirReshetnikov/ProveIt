import PA194SourceLoopTo32
import PA194Site31PhysicalClock
import PA194ActualPhysicalExit
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194MatchedLoopTo32
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopCost PA194ModelSourceLoop PA194ActualSourceLoop PA194ActualLoopOrbit PA194ControllerLoopFrame PA194OneSpareReturn PA194StateOne PA194ZeroRuns PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch PA194RegisterFile PA194RegisterPermutation PA194Path27Header
open PA194SourceSite25Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem matched (r : Fin 9 → M) (tail k n spare : M) :
    let g := (((k+1)+1)+1)
    let k' := (k+1)+r 0
    let count := (n+r 0)+r 0
    let a := frameArgs r n spare
    let a' := frameArgs (running r (r 0)) count spare
    F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![
      F (iterCode PA194ActualSourceLoop.quad) ![r 0,PA194ModelSourceLoop.source r tail]]] =
      PA194SourceSite31Controller.sourceState 32 (PA194Site31OutputFile.updated a' count) tail ∧
    ∃ time : M,
      PA194Site31AfterRun.runAfter k' count a'
        (F PA194Stepper.stepper ![PA194Site31PhysicalClock.clock24 k' count a',
          F PA194Stepper.stepper ![time,physicalFrame 27 g a]]) =
      physicalFrame 32 (k'+1) (PA194Site31OutputFile.updated a' count) := by
  dsimp only
  constructor
  · exact PA194SourceLoopTo32.reaches32 r tail k n spare
  · exact PA194PhysicalLoopTo32.reaches32 r tail k n spare
#print axioms matched
end models
end PA194MatchedLoopTo32
