import PA194Site31To71
import PA194Site27ScanRewind
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site31SecondTo17
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

theorem site31SecondTo17 (k : M) (e : Fin 11 → M) :
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
    F PA194Stepper.stepper ![F addCode ![c71,c6+cr],
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 31) ((r+r)+(r+r))]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![b,(1 : M)+out+out]] := by
  dsimp only
  let v := physicalArgs e
  let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4+1
  let a6 := a5+a5
  let n := (k+1)+1
  let a := F ones ![n,a6+a6]
  let b := F ones ![k+1,a6+a6]
  let base := (b+b+1)+(b+b+1)
  have ha : a+a=base := by
    dsimp only [a,n,base]
    rw [show (k+1)+1 = F Code.succ (fun _ => k+1) from modelAddOne _,modelOnesSucc]
  have hf : F (fileCode 10) v = p+p := by rw [modelFileSucc,modelBlock]
  have h71 := PA194Site31To71.site31To71 k e
  dsimp only at h71
  rw [ha] at h71
  have h17 := PA194Site27ScanRewind.scanAndRewind v b p hf
  dsimp only at h17
  let e6 : Fin 5 → M := fun i => v ⟨i.val+6,by omega⟩
  let q := F ones ![e6 0,F (fileCode 3) (fun i => e6 i.succ)]
  let out := F (fileCode 6) ![v 0,v 1,v 2,v 3,v 4,v 5,(q+q)+(q+q)]
  let c6 := ((((((v 0+1)+1)+((v 1+1)+1))+((v 2+1)+1))+((v 3+1)+1))+((v 4+1)+1))+((v 5+1)+1)
  let rev : Fin 6 → M := ![v 4,v 3,v 2,v 1,v 0,base]
  let cr := (modelNumeral M 2+((v 5+1)+1))+F (PA194CarryFile.costCode 5) rev
  change F PA194Stepper.stepper ![c6+cr,F pairCode ![modelNumeral M 71,F pairCode ![base,p]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![b,(1 : M)+out+out]] at h17
  rw [PA194StepperCompose.modelStepperCompose,h71,h17]
#print axioms site31SecondTo17
end models
end PA194Site31SecondTo17
