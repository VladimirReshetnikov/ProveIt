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
namespace PA194SeedFirstSite3668
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
noncomputable def stage3664 (k : M) (args : Fin 11 → M) (x : M) : M :=
    let vec := PA194Site3664MarkedFile.prefixArgs args
    let cost := ((k+1)+F (PA194CarryFile.costCode 7) vec)+modelNumeral M 2
    F PA194Stepper.stepper ![cost,
    F PA194Stepper.stepper ![modelNumeral M 9,
      F PA194Stepper.stepper ![modelNumeral M 24,
        F PA194Stepper.stepper ![((k+1)+1)+1,
          F PA194Stepper.stepper ![PA194Site3664SecondTo17.sevenCost args,
            F PA194Stepper.stepper ![modelNumeral M 3,
              F PA194Stepper.stepper ![PA194Site3664SecondTo17.clock14 k args,x]]]]]]]

theorem firstSite42To3668 (tail : M) :
    let seed := PA194SeedSecondRound.afterRound (M := M)
    let r : Fin 9 → M := fun i => seed ⟨i.val,by omega⟩
    let n := F Code.succ (fun _ => PA194SeedSecondRound.countAfterDrain (M := M))
    let spare := seed 9
    let r42 := PA194ModelTransfer42Source.running r (r 7)
    let n42 := n+r 7
    let k45 := (modelNumeral M 47+r 7)+1
    let r45 := PA194ModelTransfer45Source.running r42 (r42 6)
    let n45 := n42+r42 6
    let k48 := (k45+r42 6)+1
    let args := PA194ActualLoopOrbit.frameArgs r45 n45 spare
    ∃ c42 c45 : M,
      F PA194Stepper.stepper ![F addCode ![PA194Site3664ZeroTo16.clock (modelNumeral M 48) args,modelNumeral M 22],
        stage3664 (modelNumeral M 48) args
          (F PA194Stepper.stepper ![F addCode ![PA194Site3661ZeroTo16.clock (modelNumeral M 49) args,modelNumeral M 21],
            PA194SeedFirstSite3664.stage3661 (modelNumeral M 49) args
              (F PA194Stepper.stepper ![F addCode ![PA194Site48ZeroTo16.clock k48 args,modelNumeral M 20],
                PA194Site49ReachableGap.stage48 k48 args
                  (F PA194Stepper.stepper ![c45,F PA194Stepper.stepper ![c42,
                    physicalFrame 42 (modelNumeral M 49) seed]])])])] =
        physicalFrame 3668 (modelNumeral M 50) args ∧ args 5 = (0 : M) := by
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
  let k48 := (k45+r42 6)+1
  let args := PA194ActualLoopOrbit.frameArgs r45 n45 spare
  have hz : args 5 = (0 : M) := by
    change r45 5 = 0
    exact PA194SeedFirstSite3664Values.firstReg5Zero (M := M)
  have h50 : (modelNumeral M 48+1)+1 = modelNumeral M 50 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  obtain ⟨c42,c45,h,_⟩ := PA194SeedFirstSite3664.firstSite42To3664 (M := M) tail
  dsimp only at h
  rw [←h50] at h
  have hzero := (PA194SourceSite3664ZeroPhysical.zeroBranch (modelNumeral M 48) tail args hz).2
  refine ⟨c42,c45,?_,hz⟩
  rw [h]
  change F PA194Stepper.stepper ![_,PA194Site3664Branch.runTo4 (modelNumeral M 48) args] = _
  rw [hzero,h50]
#print axioms firstSite42To3668
end models
end PA194SeedFirstSite3668
