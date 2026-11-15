import PA194Site46ToHeaderReturn
import PA194Site46HeaderReturn
import PA194Site46OutputFile
import PA194Site32ZeroPath
import PA194Site46To7Increment
import PA194Site46MarkedFile
import PA194Site46IncrementReturn
import PA194Site46IncrementSelected
import PA194Site35ReturnPrefix
import PA194Site31Selected
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site46Complete
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ZeroRuns PA194Path27Header PA194BinaryDouble PA194FiniteControls PA194Site32ZeroPath PA194RegisterPermutation PA194RegisterFile PA194MarkedFile PA194CarryFile PA194UnaryRuns PA194OnesCommute PA194RightRows PA194StateOne PA194ReturnFile
open BinaryTapeCodes TableDispatch PA194OneSpareReturn
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem complete (k count : M) (args : Fin 11 → M)
    (he : physicalArgs args 10 = F repeatOutput ![count,(0 : M)]) :
    let d := modelNumeral M 412
    let v := physicalArgs args
    let e : Fin 7 → M := fun i => v ⟨i.val+4,by omega⟩
    let marked := F (markedFile 5) e
    let ep : Fin 5 → M := ![v 0,v 1,v 2,v 3,marked]
    let file := F (fileCode 4) ep
    let pl := F (PA194PrefixFile.leftCode 4) (Fin.cases (F ones ![k+1,d+d]) ep)
    let c := F (costCode 5) (fun i => e i.succ)
    let front := (((1 : M)+1)+e 0)+c
    let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
    let tail := F repeatOutput ![count,six]
    let rest := F (returnCode 5) (Fin.cases tail (fun i => e i.succ))
    let result := F block ![e 0+1,rest]
    let out := F (returnCode 4) (Fin.cases result ep)
    let a := F ones ![k,(1 : M)+out+out]
    let outer : M → M := fun x =>
      F PA194Stepper.stepper ![modelNumeral M 23,
        F PA194Stepper.stepper ![((1 : M)+k)+modelNumeral M 3,
          F PA194Stepper.stepper ![((modelNumeral M 2+1)+k)+1,
            F PA194Stepper.stepper ![modelNumeral M 2,x]]]]
    outer (
    F PA194Stepper.stepper ![(k+1)+1,
      F PA194Stepper.stepper ![F (costCode 4) ep,
    F PA194Stepper.stepper ![((e 0+1)+1+1),
      F PA194Stepper.stepper ![c,
        F PA194Stepper.stepper ![(count+count)+count,
          F PA194Stepper.stepper ![modelNumeral M 2,
            F PA194Stepper.stepper ![modelNumeral M 3,
              F PA194Stepper.stepper ![(count+count)+count,
                F PA194Stepper.stepper ![(1 : M),
                  F PA194Stepper.stepper ![front,
                    F PA194Stepper.stepper ![F (costCode 4) ep,
                      F PA194Stepper.stepper ![k+1,PA194Site46To7Increment.runTo2 k args]]]]]]]]]]]] ) =
    PA194SourceSite31Physical.physicalFrame 47 ((k+1)+1) (PA194Site46OutputFile.updated args count) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  dsimp only
  let v := physicalArgs args
  let e : Fin 7 → M := fun i => v ⟨i.val+4,by omega⟩
  let marked := F (markedFile 5) e
  let ep : Fin 5 → M := ![v 0,v 1,v 2,v 3,marked]
  let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
  let tail := F repeatOutput ![count,six]
  let rest := F (returnCode 5) (Fin.cases tail (fun i => e i.succ))
  let result := F block ![e 0+1,rest]
  let out := F (returnCode 4) (Fin.cases result ep)
  let q := F (returnCode 3) (Fin.cases result (fun i => ep i.succ))
  let p := F ones ![ep 0,q+q+1]
  let z := F zeros ![k,(1 : M)+out+out]
  have hout : out=p+p := by
    dsimp only [out,p,q]
    rw [modelReturnCodeSucc]
    rfl
  have houtput := PA194Site46OutputFile.outputFile args count
  dsimp only at houtput
  change F sourceFileCode (PA194Site46OutputFile.updated args count) = out at houtput
  have hi := PA194Site46ToHeaderReturn.toHeaderReturn k count args he
  dsimp only at hi
  have h812 : modelNumeral M 412 = modelNumeral M 206+modelNumeral M 206 := by rw [←modelNumeralAdd]
  rw [h812,(modelDouble (modelNumeral M 206)).1,(modelDouble (modelNumeral M 206)).2,zero_add] at hi
  change _ = F pairCode ![modelNumeral M 7,F pairCode ![modelNumeral M 206,
    (F ones ![k,(1 : M)+out+out]+F ones ![k,(1 : M)+out+out])+
    (F ones ![k,(1 : M)+out+out]+F ones ![k,(1 : M)+out+out])]] at hi
  rw [hout] at hi
  have hh := PA194Site46HeaderReturn.headerTo24 k p
  dsimp only at hh
  have hpath : PA194SourceProgram.path 47 = [true,false,false,true,true,true,true] := by decide +kernel
  have hzrun : F zeros ![(k+1)+1,(1 : M)+out+out] = (z+z)+(z+z) := by
    dsimp only [z]
    rw [PA194Site32ZeroPath.zerosSucc,PA194Site32ZeroPath.zerosSucc]
  have hword : modelWord [true,false,false,true,true,true,true]
      ((z+z)+(z+z)) = modelWord (PA194SourceProgram.path 47) (F zeros ![(k+1)+1,(1 : M)+out+out]) := by
    rw [hpath,hzrun]
  have hw : F zeros ![k,(1 : M)+(p+p)+(p+p)] = z := by
    dsimp only [z]
    rw [hout]
  rw [hw, hword] at hh
  rw [hi,hh]
  change _ = F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 47) (F zeros ![(k+1)+1,(1 : M)+(F sourceFileCode (PA194Site46OutputFile.updated args count)+F sourceFileCode (PA194Site46OutputFile.updated args count))])]]
  rw [houtput]
  simp only [add_assoc]
#print axioms complete
end models
end PA194Site46Complete
