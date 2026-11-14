import PA194OnesCommute
import PA194State42Boundary
import PA194PositiveMarkCycle
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstThreeFileCases
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAExhaustion PA194RegisterFile PA194OnesCommute PA194State42Boundary PA194PositiveMarkCycle
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

/-- The actual nonempty file makes the boundary bit distinguish the
selected zero case from a selected successor. -/
theorem selectedFileCases (n : Nat) (rest : Fin (n+2) → M) (v : M) :
    let tail := F (fileCode (n+1)) rest
    let t := F ones ![v,tail]
    (v=(0 : M) ∧ ∃ q : M, t=(q+q+1)+(q+q+1)) ∨
      (∃ k q : M, v=k+1 ∧ t=q+q+1) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let tail := F (fileCode (n+1)) rest
  have hex := modelZeroOrSuccPred v
  change v = (0 : M) ∨ F Code.succ (fun _ => F predCode (fun _ => v)) = v at hex
  rcases hex with hv | hv
  · left
    refine ⟨hv,F ones ![rest 0,F (fileCode n) (fun i => rest i.succ)],?_⟩
    rw [hv,modelOnesZero,modelFileSucc,modelBlock]
    have hs (x y : M) : F ones ![x+1,y] = F ones ![x,y]+F ones ![x,y]+1 := by
      change F ones ![F addCode ![x,F oneCode Fin.elim0],y] = _
      rw [modelAddOne,modelOnesSucc]
    rw [hs]
  · right
    let k := F predCode (fun _ => v)
    have hk : v=k+1 := by
      have ha : F Code.succ (fun _ => k) = k+1 := (modelAddOne k).symm
      exact hv.symm.trans ha
    refine ⟨k,F ones ![k,tail],hk,?_⟩
    rw [hk]
    change F ones ![F addCode ![k,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
#print axioms selectedFileCases
end models
end PA194FirstThreeFileCases
