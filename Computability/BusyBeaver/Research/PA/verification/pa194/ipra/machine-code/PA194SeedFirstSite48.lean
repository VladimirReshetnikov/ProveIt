import PA194Transfer42PhysicalExit
import PA194Transfer45PhysicalExit
import PA194SeedSite42Frame
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA194SeedFirstSite48
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
theorem firstSite42To48 (tail : M) :
    let seed := PA194SeedSecondRound.afterRound (M := M)
    let r : Fin 9 → M := fun i => seed ⟨i.val,by omega⟩
    let n := F Code.succ (fun _ => PA194SeedSecondRound.countAfterDrain (M := M))
    let spare := seed 9
    let r42 := PA194ModelTransfer42Source.running r (r 7)
    let n42 := n+r 7
    let k45 := (modelNumeral M 47+r 7)+1
    let r45 := PA194ModelTransfer45Source.running r42 (r42 6)
    let n45 := n42+r42 6
    let args := PA194ActualLoopOrbit.frameArgs r45 n45 spare
    ∃ c42 c45 : M,
      F PA194Stepper.stepper ![c45,F PA194Stepper.stepper ![c42,
        physicalFrame 42 (modelNumeral M 49) seed]] =
          physicalFrame 48 (((((k45+r42 6)+1)+1)+1)) args ∧
      args 3 = (0 : M) := by
  dsimp only
  let seed := PA194SeedSecondRound.afterRound (M := M)
  let r : Fin 9 → M := fun i => seed ⟨i.val,by omega⟩
  let n := F Code.succ (fun _ => PA194SeedSecondRound.countAfterDrain (M := M))
  let spare := seed 9
  let r42 := PA194ModelTransfer42Source.running r (r 7)
  let n42 := n+r 7
  let k45 := (modelNumeral M 47+r 7)+1
  let r45 := PA194ModelTransfer45Source.running r42 (r42 6)
  let n45 := n42+r42 6
  let args := PA194ActualLoopOrbit.frameArgs r45 n45 spare
  have h42 := PA194Transfer42PhysicalExit.completeExit r tail (modelNumeral M 47) n spare
  have h45 := PA194Transfer45PhysicalExit.completeExit r42 tail k45 n42 spare
  dsimp only at h42 h45
  have h49 : (modelNumeral M 47+1)+1 = modelNumeral M 49 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  rw [h49,PA194SeedSite42Frame.firstFrame] at h42
  have hz : args 3 = (0 : M) := by
    change r45 3 = (0 : M)
    exact PA194SeedSite42Values.firstSite48Reg3Zero
  exact ⟨_,_,by rw [h42,h45],hz⟩
#print axioms firstSite42To48
end models
end PA194SeedFirstSite48
