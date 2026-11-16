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
namespace PA194SeedFirstSite3672
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
noncomputable def stageTo2 (k : M) (args : Fin 11 → M) (x : M) : M :=
  let e := physicalArgs args
  F PA194Stepper.stepper ![modelNumeral M 9,
    F PA194Stepper.stepper ![modelNumeral M 20,F PA194Stepper.stepper ![((k+1)+1)+1,
      F PA194Stepper.stepper ![(e 0+1)+1,
        F PA194Stepper.stepper ![(e 1+1)+1,
          F PA194Stepper.stepper ![PA194Site3671SecondTo17.sixCost args,
            F PA194Stepper.stepper ![modelNumeral M 3,
              F PA194Stepper.stepper ![PA194Site3671SecondTo14.clock k args,
                x]]]]]]]]

noncomputable def stage3671 (k count : M) (args : Fin 11 → M) (x : M) : M :=
    let d := modelNumeral M 28
    let v := physicalArgs args
    let e : Fin 3 → M := fun i => v ⟨i.val+8,by omega⟩
    let marked := F (markedFile 1) e
    let ep : Fin 9 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,marked]
    let file := F (fileCode 8) ep
    let pl := F (PA194PrefixFile.leftCode 8) (Fin.cases (F ones ![k+1,d+d]) ep)
    let c := F (costCode 1) (fun i => e i.succ)
    let front := (((1 : M)+1)+e 0)+c
    let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
    let tail := F repeatOutput ![count,six]
    let rest := F (returnCode 1) (Fin.cases tail (fun i => e i.succ))
    let result := F block ![e 0+1,rest]
    let out := F (returnCode 8) (Fin.cases result ep)
    let a := F ones ![k,(1 : M)+out+out]
    let outer : M → M := fun x =>
      F PA194Stepper.stepper ![modelNumeral M 19,
        F PA194Stepper.stepper ![((1 : M)+k)+modelNumeral M 3,
          F PA194Stepper.stepper ![((modelNumeral M 2+1)+k)+1,
            F PA194Stepper.stepper ![modelNumeral M 2,x]]]]
    outer (
    F PA194Stepper.stepper ![(k+1)+1,
      F PA194Stepper.stepper ![F (costCode 8) ep,
    F PA194Stepper.stepper ![((e 0+1)+1+1),
      F PA194Stepper.stepper ![c,
        F PA194Stepper.stepper ![(count+count)+count,
          F PA194Stepper.stepper ![modelNumeral M 2,
            F PA194Stepper.stepper ![modelNumeral M 3,
              F PA194Stepper.stepper ![(count+count)+count,
                F PA194Stepper.stepper ![(1 : M),
                  F PA194Stepper.stepper ![front,
                    F PA194Stepper.stepper ![F (costCode 8) ep,
                      F PA194Stepper.stepper ![k+1,stageTo2 k args x]]]]]]]]]]]] )

theorem firstSite42To3672 (tail : M) :
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
      stage3671 (modelNumeral M 52) n45 args
          (F PA194Stepper.stepper ![F addCode ![PA194Site3668ZeroTo16.clock (modelNumeral M 48) args,modelNumeral M 18],
        PA194SeedFirstSite3671.stage3668 (modelNumeral M 48) args
          (F PA194Stepper.stepper ![F addCode ![PA194Site3664ZeroTo16.clock (modelNumeral M 48) args,modelNumeral M 22],
        PA194SeedFirstSite3668.stage3664 (modelNumeral M 48) args
          (F PA194Stepper.stepper ![F addCode ![PA194Site3661ZeroTo16.clock (modelNumeral M 49) args,modelNumeral M 21],
            PA194SeedFirstSite3664.stage3661 (modelNumeral M 49) args
              (F PA194Stepper.stepper ![F addCode ![PA194Site48ZeroTo16.clock k48 args,modelNumeral M 20],
                PA194Site49ReachableGap.stage48 k48 args
                  (F PA194Stepper.stepper ![c45,F PA194Stepper.stepper ![c42,
                    physicalFrame 42 (modelNumeral M 49) seed]])])])])]) =
        physicalFrame 3672 (modelNumeral M 54) (PA194Site39OutputFile.updated args n45) := by
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
  have hs : physicalArgs args 10 = F repeatOutput ![n45,(0 : M)] := PA194SeedFirstSite3671Suffix.firstSuffix (M := M)
  have h54 : (modelNumeral M 52+1)+1 = modelNumeral M 54 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  obtain ⟨c42,c45,h,_⟩ := PA194SeedFirstSite3671.firstSite42To3671 (M := M) tail
  dsimp only at h
  rw [←h54] at h
  have hinc := (PA194SourceSite3671Physical.sourcePhysical (modelNumeral M 52) n45 tail args hs).2
  dsimp only at hinc
  refine ⟨c42,c45,?_⟩
  rw [h]
  change _ = physicalFrame 3672 (modelNumeral M 54) (PA194Site39OutputFile.updated args n45)
  rw [←h54]
  exact hinc
#print axioms firstSite42To3672
end models
end PA194SeedFirstSite3672
