import PA194Site32MarkedTo60
import PA194Site29ScanTo71
import PA194SecondHeaderFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32SecondTo71
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site32MarkedTo60 PA194Site29ScanTo71 PA194Path27Header PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194FiniteControls PA194StateOne PRAModelIOpenPairing
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
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let a6 := a5+a5+1
    let l := (a6+a6)+(a6+a6)
    let tail := F ones ![v 2+1,F (fileCode 7) (fun i => v i.succ.succ.succ)]
    let l0 := F ones ![k,l]
    let l1 := l0+l0+1
    let l2 := l1+l1+1
    let l3 := l2+l2
    let l4 := F ones ![v 0+1,l3]
    let l5 := l4+l4
    let l6 := F ones ![v 1+1,l5]
    let cscan := ((k+modelNumeral M 3)+((v 0+1)+1))+((v 1+1)+1)
    let c13 := F addCode ![F addCode ![F addCode ![modelNumeral M 8,modelNumeral M 3],(1 : M)],(1 : M)]
    F PA194Stepper.stepper ![F addCode ![c13,cscan],
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 32) w]]] =
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
  let a5 := a4+a4+1
  let a6 := a5+a5+1
  let l := (a6+a6)+(a6+a6)
  let c13 := F addCode ![F addCode ![F addCode ![modelNumeral M 8,modelNumeral M 3],(1 : M)],(1 : M)]
  let cscan := ((k+modelNumeral M 3)+((v 0+1)+1))+((v 1+1)+1)
  have hf : F (fileCode 8) (fun i => v i.succ.succ) = tail+tail := by
    rw [modelFileSucc,modelBlock]
    rfl
  have h13 := PA194Site32MarkedTo60.markedTo60 (M := M) (1 : M) r
  dsimp only at h13
  have hs := PA194Site29ScanTo71.scanTo71 (M := M) k (v 0) (v 1) l tail
  dsimp only at hs
  rw [←hf] at hs
  have ht : t = ((p+p)+(p+p)+1)+((p+p)+(p+p)+1)+1 := by
    dsimp only [t]
    simp only [add_assoc,add_comm,add_left_comm]
  rw [←ht] at hs
  change F PA194Stepper.stepper ![F addCode ![c13,cscan],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h13,hs]
#print axioms secondPassTo71
end models
end PA194Site32SecondTo71
