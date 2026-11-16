import PA194Site29SecondDispatch
import PA194Site29ScanTo71
import PA194SecondHeaderFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29SecondPassTo71
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site29SecondDispatch PA194Site29ScanTo71 PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194FiniteControls PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem secondPassTo71 (k : M) (args : Fin 11 → M) :
    let v := physicalArgs args
    let b := F ones ![v 1+1,F (fileCode 8) (fun i => v i.succ.succ)]
    let p := F ones ![v 0+1,b+b]
    let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
    let r := F ones ![k,t]
    let w := r+r+1
    let r2 := w+w
    let u0 := r2+r2+1
    let u1 := u0+u0+1
    let u2 := u1+u1
    let u3 := u2+u2+1
    let u4 := u3+u3
    let u5 := u4+u4
    let u6 := u5+u5
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a := a4+a4
    let bb := a+a+1
    let cc := bb+bb+1
    let d := cc+cc
    let l := d+d
    let tail := F ones ![v 2+1,F (fileCode 7) (fun i => v i.succ.succ.succ)]
    let l0 := F ones ![k,l]
    let l1 := l0+l0+1
    let l2 := l1+l1+1
    let l3 := l2+l2
    let l4 := F ones ![v 0+1,l3]
    let l5 := l4+l4
    let l6 := F ones ![v 1+1,l5]
    let cscan := ((k+modelNumeral M 3)+((v 0+1)+1))+((v 1+1)+1)
    F PA194Stepper.stepper ![modelNumeral M 18+cscan,
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),u6+u6+1]]] =
    F pairCode ![modelNumeral M 71,F pairCode ![l6+l6,tail]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let v := physicalArgs args
  let tail := F ones ![v 2+1,F (fileCode 7) (fun i => v i.succ.succ.succ)]
  let b := F ones ![v 1+1,F (fileCode 8) (fun i => v i.succ.succ)]
  let p := F ones ![v 0+1,b+b]
  let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
  let r := F ones ![k,t]
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a := a4+a4
  let bb := a+a+1
  let cc := bb+bb+1
  let d := cc+cc
  let l := d+d
  let cscan := ((k+modelNumeral M 3)+((v 0+1)+1))+((v 1+1)+1)
  have hf : F (fileCode 8) (fun i => v i.succ.succ) = tail+tail := by
    rw [modelFileSucc,modelBlock]
    rfl
  have h18 := PA194Site29SecondDispatch.eighteenTo60 (M := M) (1 : M) r
  dsimp only at h18
  have hs := PA194Site29ScanTo71.scanTo71 (M := M) k (v 0) (v 1) l tail
  dsimp only at hs
  rw [←hf] at hs
  have ht : t = ((p+p)+(p+p)+1)+((p+p)+(p+p)+1)+1 := by
    dsimp only [t]
    simp only [add_assoc,add_comm,add_left_comm]
  rw [←ht] at hs
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 18,cscan],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h18,hs]
#print axioms secondPassTo71
end models
end PA194Site29SecondPassTo71
