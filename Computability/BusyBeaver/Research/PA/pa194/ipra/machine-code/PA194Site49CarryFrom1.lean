import PA194Site49MarkedFile
import PA194Site48CarryTo4
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site49CarryFrom1
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194MarkedFile PA194CarryFile PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes PA194UnaryRuns PA194StateOne TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem carry (k : M) (args : Fin 11 → M) :
    let e := PA194Site49MarkedFile.selectedArgs args
    let tail := F (fileCode 5) (fun i => e i.succ)
    let q := F ones ![e 0,tail]
    let vec := PA194Site49MarkedFile.prefixArgs args
    let before := F ones ![k+1,modelNumeral M 1696]
    let left := F (PA194CarryFile.leftCode 4) (Fin.cases before vec)
    let z := left+left+1
    let cost := ((k+1)+F (PA194CarryFile.costCode 4) vec)+modelNumeral M 2
    F PA194Stepper.stepper ![cost,F pairCode ![(1 : M),F pairCode ![modelNumeral M 1696,F halfCode (fun _ => PA194Site49SecondTo17.output k args)]]] =
      F pairCode ![modelNumeral M 4,F pairCode ![z+z,q]] := by
  dsimp only
  let v := physicalArgs args
  let vec := PA194Site49MarkedFile.prefixArgs args
  let file := F (fileCode 4) vec
  have hf := PA194Site49MarkedFile.markedInput k args
  change F halfCode (fun _ => PA194Site49SecondTo17.output k args) = F ones ![k,file+file+1] at hf
  let e := PA194Site49MarkedFile.selectedArgs args
  let tail := F (fileCode 5) (fun i => e i.succ)
  let q := F ones ![e 0,tail]
  have hm : F (markedFile 5) e = (q+q)+(q+q) := by
    rw [modelMarkedFile,modelMarkedBlock]
  have hv : vec = ![v 0,v 1,v 2,v 3,(q+q)+(q+q)] := by
    dsimp only [vec,PA194Site49MarkedFile.prefixArgs]
    rw [hm]
  rw [hf]
  change F PA194Stepper.stepper ![((k+1)+F (costCode 4) vec)+modelNumeral M 2,
    F pairCode ![(1 : M),F pairCode ![modelNumeral M 1696,F ones ![k,F (fileCode 4) vec+F (fileCode 4) vec+1]]]] =
    F pairCode ![modelNumeral M 4,F pairCode ![(F (leftCode 4) (Fin.cases (F ones ![k+1,modelNumeral M 1696]) vec)+F (leftCode 4) (Fin.cases (F ones ![k+1,modelNumeral M 1696]) vec)+1)+
      (F (leftCode 4) (Fin.cases (F ones ![k+1,modelNumeral M 1696]) vec)+F (leftCode 4) (Fin.cases (F ones ![k+1,modelNumeral M 1696]) vec)+1),q]]
  rw [hv]
  have hc := PA194Site48CarryTo4.carryTo4 k (modelNumeral M 1696) v
  dsimp only at hc
  rw [modelNumeralOne] at hc
  exact hc
#print axioms carry
end models
end PA194Site49CarryFrom1
