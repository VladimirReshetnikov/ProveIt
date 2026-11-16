import PA194SeedFirstDecodeComplete
import PA194ModelTransfer42Source
import PA194ModelTransfer45Source
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SeedSite42Values
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194SeedFrameAlignment PA194StartupSourceFrame PA194SeedToFirstSite35 PA194ActualLoopOrbit PA194RegisterPermutation TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem reg6Zero : PA194SeedSecondRound.afterRound (M := M) 6 = (0 : M) := by
  simp [PA194SeedSecondRound.afterRound]

theorem reg7One : PA194SeedSecondRound.afterRound (M := M) 7 = (1 : M) := by
  simp [PA194SeedSecondRound.afterRound,PA194Site35OutputFile.updated,PA194SeedAfterDrainValues.reg7Zero]

theorem reg3Zero : PA194SeedSecondRound.afterRound (M := M) 3 = (0 : M) := by
  simp [PA194SeedSecondRound.afterRound, PA194Site35OutputFile.updated,
    PA194SeedToDrainReturn.afterDrain, PA194Site39OutputFile.updated,
    PA194SeedToFirstSite36.args36, next35, out34, PA194Site31OutputFile.updated,
    PA194ActualLoopOrbit.frameArgs, PA194ActualSourceLoop.args,
    PA194ModelRestoreSource.running, PA194ModelSourceLoop.running,
    seedRegs, seedArgs30, PA194Site29OutputWithCarry.updated,
    PA194Site28OutputFile.updated, seedArgs]
  rfl
theorem firstSite48Reg3Zero :
    let r : Fin 9 → M := fun i => PA194SeedSecondRound.afterRound (M := M) ⟨i.val,by omega⟩
    let r42 := PA194ModelTransfer42Source.running r (r 7)
    let r45 := PA194ModelTransfer45Source.running r42 (r42 6)
    r45 3 = (0 : M) := by
  dsimp only
  simp [PA194ModelTransfer42Source.running,PA194ModelTransfer45Source.running,reg3Zero,reg6Zero]
#print axioms firstSite48Reg3Zero
#print axioms reg7One
#print axioms reg6Zero
#print axioms reg3Zero
end models
end PA194SeedSite42Values
