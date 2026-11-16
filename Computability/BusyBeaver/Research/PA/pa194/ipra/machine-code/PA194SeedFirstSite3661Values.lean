import PA194Transfer42PhysicalExit
import PA194Transfer45PhysicalExit
import PA194SeedFirstSite3661
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA194SeedFirstSite3661Values
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
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
theorem seedReg1Zero : PA194SeedSecondRound.afterRound (M := M) 1 = (0 : M) := by
  simp [PA194SeedSecondRound.afterRound, PA194Site35OutputFile.updated,
    PA194SeedToDrainReturn.afterDrain, PA194Site39OutputFile.updated,
    PA194SeedToFirstSite36.args36, PA194SeedToFirstSite35.next35, PA194SeedToFirstSite35.out34, PA194Site31OutputFile.updated,
    PA194ActualLoopOrbit.frameArgs, PA194ActualSourceLoop.args,
    PA194ModelRestoreSource.running, PA194ModelSourceLoop.running,
    PA194SeedFrameAlignment.seedRegs, PA194SeedFrameAlignment.seedArgs30, PA194Site29OutputWithCarry.updated,
    PA194Site28OutputFile.updated, PA194StartupSourceFrame.seedArgs]
  rfl

theorem firstReg1Zero :
    let seed := PA194SeedSecondRound.afterRound (M := M)
    let r : Fin 9 → M := fun i => seed ⟨i.val,by omega⟩
    let r42 := PA194ModelTransfer42Source.running r (r 7)
    let r45 := PA194ModelTransfer45Source.running r42 (r42 6)
    r45 1 = (0 : M) := by
  dsimp only
  simp [PA194ModelTransfer42Source.running,PA194ModelTransfer45Source.running,seedReg1Zero]

theorem firstGap :
    let seed := PA194SeedSecondRound.afterRound (M := M)
    let r : Fin 9 → M := fun i => seed ⟨i.val,by omega⟩
    let r42 := PA194ModelTransfer42Source.running r (r 7)
    let k45 := (modelNumeral M 47+r 7)+1
    ((k45+r42 6)+1)+1 = modelNumeral M 51 := by
  dsimp only
  have h6 : PA194ModelTransfer42Source.running
      (fun i : Fin 9 => PA194SeedSecondRound.afterRound (M := M) ⟨i.val,by omega⟩)
      (PA194SeedSecondRound.afterRound 7) 6 = (0 : M) := by
    simpa [PA194ModelTransfer42Source.running] using (PA194SeedSite42Values.reg6Zero (M := M))
  change (((modelNumeral M 47+PA194SeedSecondRound.afterRound 7)+1+
      PA194ModelTransfer42Source.running
        (fun i : Fin 9 => PA194SeedSecondRound.afterRound (M := M) ⟨i.val,by omega⟩)
        (PA194SeedSecondRound.afterRound 7) 6)+1)+1 = modelNumeral M 51
  rw [h6,PA194SeedSite42Values.reg7One,add_zero]
  rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd]
#print axioms seedReg1Zero
#print axioms firstReg1Zero
#print axioms firstGap
end models
end PA194SeedFirstSite3661Values
