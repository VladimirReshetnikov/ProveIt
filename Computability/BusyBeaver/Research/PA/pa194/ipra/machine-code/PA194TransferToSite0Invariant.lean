import PA194IncrementFrameInvariant
import PA194SourceSite3672Physical
import PA194SeedFirstSite3672
import PA194SeedFirstSite3671Suffix
import PA194SeedFirstSite3671
import PA194SourceSite3671Physical
import PA194SeedFirstSite3668Values
import PA194SeedFirstSite3668
import PA194SourceSite3668ZeroPhysical
import PA194SeedFirstSite3664Values
import PA194SeedFirstSite3664
import PA194SourceSite3664ZeroPhysical
import PA194SeedFirstSite3661Values
import PA194SourceSite3661ZeroPhysical
import PA194Transfer42PhysicalExit
import PA194Transfer45PhysicalExit
import PA194SeedFirstSite48
import PA194SourceSite48ZeroPhysical
import PA194Site49ReachableGap
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA194TransferToSite0Invariant
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194RegisterFile PA194OneSpareReturn PA194MarkedFile PA194CarryFile PA194ReturnFile PA194UnaryRuns PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194StateOne PA194FiniteControls PA194ModelLoopIteration PA194RegisterPermutation PA194SourceSite31Physical PA194ModelTransferState TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
noncomputable def physicalMacro (k count : M) (args : Fin 11 → M) (x : M) : M :=
  let g := ((k+1)+1)+1
  let x1 := F PA194Stepper.stepper ![F addCode ![PA194Site3661ZeroTo16.clock (k+1) args,modelNumeral M 21],
    PA194SeedFirstSite3664.stage3661 (k+1) args x]
  let x2 := F PA194Stepper.stepper ![F addCode ![PA194Site3664ZeroTo16.clock k args,modelNumeral M 22],
    PA194SeedFirstSite3668.stage3664 k args x1]
  let x3 := F PA194Stepper.stepper ![F addCode ![PA194Site3668ZeroTo16.clock k args,modelNumeral M 18],
    PA194SeedFirstSite3671.stage3668 k args x2]
  let x4 := PA194SeedFirstSite3672.stage3671 (g+1) count args x3
  F PA194Stepper.stepper ![modelNumeral M 24,x4]

theorem matchedMacro (k count spare tail : M) (r : Fin 9 → M)
    (h1 : r 1 = (0 : M)) (h5 : r 5 = (0 : M)) (h6 : r 6 = (0 : M)) :
    let g := ((k+1)+1)+1
    let args := PA194ActualLoopOrbit.frameArgs r count spare
    let args' := PA194ActualLoopOrbit.frameArgs (Function.update r 6 (r 6+1)) (count+1) spare
    let step := PA194SourceControllerCode.step
    let source := PA194SourceSite31Controller.sourceState 3661 args tail
    F step ![F step ![F step ![F step ![F step ![source]]]]] =
      PA194SourceSite31Controller.sourceState 0 args' tail ∧
    physicalMacro k count args (physicalFrame 3661 g args) = physicalFrame 0 g args' := by
  dsimp only
  let g := ((k+1)+1)+1
  let args := PA194ActualLoopOrbit.frameArgs r count spare
  let args' := PA194ActualLoopOrbit.frameArgs (Function.update r 6 (r 6+1)) (count+1) spare
  have ha1 : args 1 = (0 : M) := by simpa [args,PA194ActualLoopOrbit.frameArgs,PA194ActualSourceLoop.args,Function.update] using h1
  have ha5 : args 5 = (0 : M) := by simpa [args,PA194ActualLoopOrbit.frameArgs,PA194ActualSourceLoop.args,Function.update] using h5
  have ha6 : args 6 = (0 : M) := by simpa [args,PA194ActualLoopOrbit.frameArgs,PA194ActualSourceLoop.args,Function.update] using h6
  have hsuffix : physicalArgs args 10 = F repeatOutput ![count,(0 : M)] := by
    simp [args,PA194RegisterPermutation.physicalArgs,PA194RegisterPermutation.inputOrder,PA194ActualLoopOrbit.frameArgs,Function.update]
  have hout : PA194Site39OutputFile.updated args count = args' := PA194IncrementFrameInvariant.incrementPreservesFrame r count spare
  have hstep1 := PA194SourceSite3661ZeroPhysical.zeroBranch (k+1) tail args ha1
  have hstep2 := PA194SourceSite3664ZeroPhysical.zeroBranch k tail args ha5
  have hstep3 := PA194SourceSite3668ZeroPhysical.zeroBranch k tail args ha6
  have hstep4 := PA194SourceSite3671Physical.sourcePhysical (g+1) count tail args hsuffix
  have hstep5 := PA194SourceSite3672Physical.sourcePhysical g tail (PA194Site39OutputFile.updated args count)
  have hp1 := hstep1.2
  have hp2 := hstep2.2
  have hp3 := hstep3.2
  have hp4 := hstep4.2
  have hp5 := hstep5.2
  dsimp only at hp4
  have hphys1 : F PA194Stepper.stepper ![F addCode ![PA194Site3661ZeroTo16.clock (k+1) args,modelNumeral M 21],
      PA194SeedFirstSite3664.stage3661 (k+1) args (physicalFrame 3661 g args)] = physicalFrame 3664 ((k+1)+1) args := hp1
  have hphys2 : F PA194Stepper.stepper ![F addCode ![PA194Site3664ZeroTo16.clock k args,modelNumeral M 22],
      PA194SeedFirstSite3668.stage3664 k args (physicalFrame 3664 ((k+1)+1) args)] = physicalFrame 3668 ((k+1)+1) args := hp2
  have hphys3 : F PA194Stepper.stepper ![F addCode ![PA194Site3668ZeroTo16.clock k args,modelNumeral M 18],
      PA194SeedFirstSite3671.stage3668 k args (physicalFrame 3668 ((k+1)+1) args)] =
        physicalFrame 3671 (((((k+1)+1)+1)+1)+1+1) args := hp3
  have hphys4 : PA194SeedFirstSite3672.stage3671 (g+1) count args
      (physicalFrame 3671 (((((k+1)+1)+1)+1)+1+1) args) =
        physicalFrame 3672 (((((k+1)+1)+1)+1)+1+1) (PA194Site39OutputFile.updated args count) := hp4
  constructor
  · rw [hstep1.1,hstep2.1,hstep3.1,hstep4.1,hstep5.1,hout]
  · dsimp only [physicalMacro]
    rw [hphys1,hphys2,hphys3,hphys4,hp5,hout]
#print axioms matchedMacro
end models
end PA194TransferToSite0Invariant
