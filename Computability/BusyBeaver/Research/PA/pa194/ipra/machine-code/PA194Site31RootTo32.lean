import PA194Site31AfterRun
import PA194Site31SecondRoot
import PA194Site31RootTo2
import PA194Site27ScanRewind
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site31RootTo32
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site31To71 PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PRAModelIOpenPairing PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem rootTo32 (k count : M) (e : Fin 11 → M)
    (he : physicalArgs e 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)]) :
    let v := physicalArgs e
    let f := F sourceFileCode e
    let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
    let r := F zeros ![k,f+f+1]
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let a6 := a5+a5
    let n := (k+1)+1
    let b := F ones ![k+1,a6+a6]
    let base := (b+b+1)+(b+b+1)
    let e6 : Fin 5 → M := fun i => v ⟨i.val+6,by omega⟩
    let q := F ones ![e6 0,F (fileCode 3) (fun i => e6 i.succ)]
    let out := F (fileCode 6) ![v 0,v 1,v 2,v 3,v 4,v 5,(q+q)+(q+q)]
    let c6 := ((((((v 0+1)+1)+((v 1+1)+1))+((v 2+1)+1))+((v 3+1)+1))+((v 4+1)+1))+((v 5+1)+1)
    let rev : Fin 6 → M := ![v 4,v 3,v 2,v 1,v 0,base]
    let cr := (modelNumeral M 2+((v 5+1)+1))+F (PA194CarryFile.costCode 5) rev
    let c15 := F addCode ![F addCode ![modelNumeral M 7,modelNumeral M 3],modelNumeral M 5]
    let c := (((((k+1)+1)+1)+1)+((k+1)+1))
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let cpass := F addCode ![F addCode ![c15,c],F addCode ![modelNumeral M 2,modelNumeral M 3+rc]]
    let c106 := F addCode ![modelNumeral M 7,modelNumeral M 1]
    let c71 := F addCode ![F addCode ![cpass,c106],n+1]
    let croot := (((((1 : M)+k)+1)+1)+(modelNumeral M 3+(modelNumeral M 3+rc)))
    let w := F ones ![k+1,out+out+1]
    let w1 := w+w
    let w2 := w1+w1
    let w3 := w2+w2
    let u := (1 : M)+w3
    let t := (1 : M)+u+u
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    let x := F ones ![k,out+out+1]
    let h0 := (1 : M)+(1 : M)+1
    let h1 := h0+h0
    let h2 := h1+h1
    let h3 := h2+h2
    let h4 := h3+h3+1
    let h5 := h4+h4+1
    let h6 := h5+h5
    let h7 := h6+h6
    let h8 := h7+h7
    let cthird := F addCode ![F addCode ![modelNumeral M 7,modelNumeral M 3],modelNumeral M 5]
    let marked := F (PA194MarkedFile.markedFile 3) e6
    let ep : Fin 7 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,marked]
    let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
    let tail := F PA194OneSpareReturn.repeatOutput ![count,six]
    let rest := F (PA194ReturnFile.returnCode 3) (Fin.cases tail (fun i => e6 i.succ))
    let result := F block ![e6 0+1,rest]
    let newFile := F (PA194ReturnFile.returnCode 6) (Fin.cases result ep)
    let z := F zeros ![k,(1 : M)+newFile+newFile]
    PA194Site31AfterRun.runAfter k count e (
    F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![c71,c6+cr],croot],cthird],
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 31) ((r+r)+(r+r))]]]) =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),
      modelWord (PA194SourceProgram.path 32) (z+z)]] := by
  dsimp only
  let v := physicalArgs e
  let e6 : Fin 5 → M := fun i => v ⟨i.val+6,by omega⟩
  let q := F ones ![e6 0,F (fileCode 3) (fun i => e6 i.succ)]
  have hm : F (PA194MarkedFile.markedFile 3) e6 = (q+q)+(q+q) := by
    rw [PA194MarkedFile.modelMarkedFile,PA194MarkedFile.modelMarkedBlock]
  let out := F (fileCode 6) ![v 0,v 1,v 2,v 3,v 4,v 5,(q+q)+(q+q)]
  let ep : Fin 7 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,F (PA194MarkedFile.markedFile 3) e6]
  let file := F (fileCode 6) ep
  let h0 := (1 : M)+(1 : M)+1
  let h1 := h0+h0
  let h2 := h1+h1
  let h3 := h2+h2
  let h4 := h3+h3+1
  let h5 := h4+h4+1
  let h6 := h5+h5
  let h7 := h6+h6
  let h8 := h7+h7
  have hout : file=out := by
    dsimp only [file,out,ep]
    rw [hm]
  have hroot := PA194Site31To2.site31To2 k e
  dsimp only at hroot
  change _ = F pairCode ![modelNumeral M 2,F pairCode ![h8,F ones ![k,out+out+1]]] at hroot
  rw [←hout] at hroot
  have hafter := PA194Site31AfterSelectedTo32.afterSelectedTo32 k count e he
  dsimp only at hafter
  unfold PA194Site31AfterRun.runAfter
  dsimp only
  rw [hroot,hafter]
#print axioms rootTo32
end models
end PA194Site31RootTo32
