import PA194MatchedLoopTo32
import PA194SourceSite32BothPhysical
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194MatchedLoopAfter32
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
    let output := PA194Site31OutputFile.updated a' count
    let source := F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![
      F (iterCode PA194ActualSourceLoop.quad) ![r 0,PA194ModelSourceLoop.source r tail]]]
    ∃ time : M,
      let physical := PA194Site31AfterRun.runAfter k' count a'
        (F PA194Stepper.stepper ![PA194Site31PhysicalClock.clock24 k' count a',
          F PA194Stepper.stepper ![time,physicalFrame 27 g a]])
      (output 6 = (0 : M) ∧ F PA194SourceControllerCode.step ![source] =
          PA194SourceSite31Controller.sourceState 34 output tail ∧
        ∃ clock : M, F PA194Stepper.stepper ![clock,physical] =
          PA194SourceSite31Physical.physicalFrame 34 ((((k+r 0)+1)+1)+1) output) ∨
      (∃ m : M, output 6 = m+1 ∧ F PA194SourceControllerCode.step ![source] =
          PA194SourceSite31Controller.sourceState 33 (Function.update output 6 m) tail ∧
        ∃ clock : M, F PA194Stepper.stepper ![clock,physical] =
          PA194SourceSite31Physical.physicalFrame 33 ((((k+r 0)+1)+1)+1) (Function.update output 6 m)) := by
  dsimp only
  let count := (n+r 0)+r 0
  let a' := frameArgs (running r (r 0)) count spare
  let output := PA194Site31OutputFile.updated a' count
  have h32 := PA194MatchedLoopTo32.matched r tail k n spare
  dsimp only at h32
  obtain ⟨hs,time,hphysical⟩ := h32
  have hgap : ((k+1)+r 0)+1 = ((k+r 0)+1)+1 := by simp only [add_assoc,add_comm,add_left_comm]
  rw [hgap] at hphysical
  change PA194Site31AfterRun.runAfter ((k+1)+r 0) count a'
    (F PA194Stepper.stepper ![PA194Site31PhysicalClock.clock24 ((k+1)+r 0) count a',
      F PA194Stepper.stepper ![time,physicalFrame 27 (((k+1)+1)+1) (frameArgs r n spare)]]) =
    PA194SourceSite31Physical.physicalFrame 32 (((k+r 0)+1)+1) output at hphysical
  have cases := PA194SourceSite32BothPhysical.bothBranches (k+r 0) tail output
  refine ⟨time,?_⟩
  rcases cases with hzero | hpositive
  · obtain ⟨hz,hsource,clock,hphysical34⟩ := hzero
    left
    refine ⟨hz,?_,clock,?_⟩
    · rw [hs]; exact hsource
    · rw [hphysical]; exact hphysical34
  · obtain ⟨m,hm,hsource,clock,hphysical33⟩ := hpositive
    right
    refine ⟨m,hm,?_,clock,?_⟩
    · rw [hs]; exact hsource
    · rw [hphysical]; exact hphysical33
#print axioms matched
end models
end PA194MatchedLoopAfter32
