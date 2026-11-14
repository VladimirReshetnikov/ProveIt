import PA194FirstTwoPositiveTo71
import PA194GenericRightScan
import PA194State106Scan
import PA194GenericRightScan
import PA194RightRows
import PA194PositiveMarkerRoute
import PA194FirstFiveFirstCore
import PA194FirstFiveTo84
import PA194EightyFourScan
import PA194State42Boundary
import PA194PositiveMarkCycle
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194HalfFileScan
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstTwoPositiveTo71 PA194FirstTwoPositiveTo106 PA194FirstTwoPositiveTo85 PA194FirstTwoFirstTo73 PA194FirstTwoFirstTo86 PA194RightRows PA194FirstTwoBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble
open PA194PositiveThreshold PA194HeaderController PA194PositiveMarkerRoute PA194ThresholdCycle
open PA194MarkAll PA194CarryFile PA194RegisterFile PA194ReturnFile PA194MarkerScan
open PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem scanHalfBlock (n q dest : Nat) (e : Fin (n+2) → M) (l p : M)
    (hblank : e (Fin.last (n+1)) = (0 : M))
    (hp : F (fileCode (n+1)) e = p+p)
    (hloop : ∀ x y : M, F PackedClock.encodedStep (fun _ =>
      F pairCode ![modelNumeral M q,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M q,F pairCode ![x+x+1,y]])
    (hexit : ∀ x y : M, F PackedClock.encodedStep (fun _ =>
      F pairCode ![modelNumeral M q,F pairCode ![x,y+y]]) =
      F pairCode ![modelNumeral M dest,F pairCode ![x+x,y]]) :
    ∃ r : M, F (fileCode n) (fun i => e i.succ) = r+r ∧
      let x := F ones ![e 0+1,l]
      F PA194Stepper.stepper ![(e 0+1)+1,F pairCode ![modelNumeral M q,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M dest,F pairCode ![x+x,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  obtain ⟨r,hr⟩ := evenRemainingFile n e hblank
  let a := F ones ![e 0+1,r+r]
  have hf : F (fileCode (n+1)) e = a+a := by
    rw [modelFileSucc,modelBlock,hr]
  rw [hf] at hp
  have hh := congrArg (fun x : M => F halfCode (fun _ => x)) hp
  rw [(modelDouble a).2,(modelDouble p).2] at hh
  subst p
  have hs := PA194GenericRightScan.modelFullScan q hloop (e 0+1) l (r+r)
  refine ⟨r,hr,?_⟩
  dsimp only
  change F PA194Stepper.stepper ![F addCode ![e 0+1,F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc,hs,hexit]
#print axioms scanHalfBlock
end models
end PA194HalfFileScan
