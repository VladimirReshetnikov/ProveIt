import PA194OnesCommute
import PA194State42Boundary
import PA194PositiveMarkCycle
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstFiveFirstCore
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

/-- Actual first-position file data always supply the odd delimiter needed
for the state-84 scanner, in three or four zero reads. -/
theorem actualFirstCore (n : Nat) (rest : Fin (n+2) → M) (v : M) :
    let tail := F (fileCode (n+1)) rest
    let t := F ones ![v,tail]
    let a := t+t
    let b := a+a
    ∃ len q : M, (len = modelNumeral M 3 ∨ len = modelNumeral M 4) ∧
      F zeros ![len,q+q+1] = b+b := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let tail := F (fileCode (n+1)) rest
  have hz3 (x : M) : F zeros ![modelNumeral M 3,x] = ((x+x)+(x+x))+((x+x)+(x+x)) := by
    rw [show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,modelZerosSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelZerosSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelZerosSucc,
      show modelNumeral M 0 = (0 : M) from rfl,modelZerosZero]
  have hz4 (x : M) : F zeros ![modelNumeral M 4,x] =
      ((((x+x)+(x+x))+((x+x)+(x+x)))+(((x+x)+(x+x))+((x+x)+(x+x)))) := by
    rw [show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,modelZerosSucc,hz3]
  have hex := modelZeroOrSuccPred v
  change v = (0 : M) ∨ F Code.succ (fun _ => F predCode (fun _ => v)) = v at hex
  rcases hex with hv | hv
  · have htail : tail = F block ![rest 0,F (fileCode n) (fun i => rest i.succ)] := modelFileSucc n rest
    let core := F ones ![rest 0,F (fileCode n) (fun i => rest i.succ)]
    have hc : tail = (core+core+1)+(core+core+1) := by
      rw [htail,modelBlock]
      have hs : F ones ![rest 0+1,F (fileCode n) (fun i => rest i.succ)] = core+core+1 := by
        change F ones ![F addCode ![rest 0,F oneCode Fin.elim0],_] = _
        rw [modelAddOne,modelOnesSucc]
      rw [hs]
    refine ⟨modelNumeral M 4,core,Or.inr rfl,?_⟩
    rw [hv,modelOnesZero]
    change F zeros ![modelNumeral M 4,core+core+1] = ((tail+tail)+(tail+tail))+((tail+tail)+(tail+tail))
    rw [hc,hz4]
  · let k := F predCode (fun _ => v)
    have hk : v=k+1 := by
      have ha : F Code.succ (fun _ => k) = k+1 := (modelAddOne k).symm
      exact hv.symm.trans ha
    let core := F ones ![k,tail]
    have hc : F ones ![v,tail] = core+core+1 := by
      rw [hk]
      change F ones ![F addCode ![k,F oneCode Fin.elim0],_] = _
      rw [modelAddOne,modelOnesSucc]
    refine ⟨modelNumeral M 3,core,Or.inl rfl,?_⟩
    rw [hc,hz3]
#print axioms actualFirstCore
end models
end PA194FirstFiveFirstCore
