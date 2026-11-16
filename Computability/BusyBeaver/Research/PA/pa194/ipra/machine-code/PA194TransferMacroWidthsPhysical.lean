import PA194TransferToSite0Invariant
import PA194TransferMacroWidths
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
namespace PA194TransferMacroWidthsPhysical
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
theorem matchedMacroWithWidths (k count spare tail : M) (r : Fin 9 → M)
    (h1 : r 1 = (0 : M)) (h5 : r 5 = (0 : M)) (h6 : r 6 = (0 : M)) :
    let g := ((k+1)+1)+1
    let args := PA194ActualLoopOrbit.frameArgs r count spare
    let args' := PA194ActualLoopOrbit.frameArgs (Function.update r 6 (r 6+1)) (count+1) spare
    let step := PA194SourceControllerCode.step
    let source := PA194SourceSite31Controller.sourceState 3661 args tail
    F step ![F step ![F step ![F step ![F step ![source]]]]] =
      PA194SourceSite31Controller.sourceState 0 args' tail ∧
    PA194TransferToSite0Invariant.physicalMacro k count args (physicalFrame 3661 g args) = physicalFrame 0 g args' ∧
    let g2 := ((k+1)+1)
    let g3 := (((((k+1)+1)+1)+1)+1+1)
    PA194TransferMacroWidths.width 3661 g = PA194TransferMacroWidths.width 3664 g2 ∧
    PA194TransferMacroWidths.width 3664 g2 = PA194TransferMacroWidths.width 3668 g2 ∧
    PA194TransferMacroWidths.width 3668 g2 = PA194TransferMacroWidths.width 3671 g3 ∧
    PA194TransferMacroWidths.width 3671 g3 = PA194TransferMacroWidths.width 3672 g3 ∧
    PA194TransferMacroWidths.width 3672 g3 = PA194TransferMacroWidths.width 0 g := by
  dsimp only
  have hm := PA194TransferToSite0Invariant.matchedMacro k count spare tail r h1 h5 h6
  dsimp only at hm
  exact ⟨hm.1, hm.2, PA194TransferMacroWidths.macroWidths k⟩
#print axioms matchedMacroWithWidths
end models
end PA194TransferMacroWidthsPhysical
