import PA194Site28IncrementWrite
import PA194StepperCompose
import PA194RegisterFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28CarrySeven
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RightRows PA194RegisterFile PA194UnaryRuns PA194FiniteControls PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem carryCell (n l tail : M) :
    F PA194Stepper.stepper ![(1 : M)+(n+1),F pairCode ![modelNumeral M 3,
      F pairCode ![l,F ones ![n+1,tail+tail]]]] =
    F pairCode ![modelNumeral M 3,F pairCode ![F ones ![n+1,l+l],tail]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let r := F ones ![n,tail+tail]
  have ho : F ones ![n+1,tail+tail] = r+r+1 := by
    change F ones ![F addCode ![n,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have h3 := rightOne 3 0 1 (by decide) (by decide +kernel) l r
  simp only [show modelNumeral M 0 = (0 : M) from rfl,show modelNumeral M 1 = (1 : M) from modelNumeralOne,add_zero] at h3
  have hi := PA194Site28IncrementWrite.incrementWrite (M := M) n (l+l) tail
  rw [ho]
  change F PA194Stepper.stepper ![F addCode ![(1 : M),n+1],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  have hone (x : M) : F PA194Stepper.stepper ![(1 : M),x] = F PackedClock.encodedStep (fun _ => x) := by
    rw [←modelNumeralOne]
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),x] = _
    rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero]
  rw [hone,h3,hi]
theorem carrySeven (e : Fin 9 → M) (l : M) :
    let e1 : Fin 8 → M := fun i => e i.succ
    let e2 : Fin 7 → M := fun i => e1 i.succ
    let e3 : Fin 6 → M := fun i => e2 i.succ
    let e4 : Fin 5 → M := fun i => e3 i.succ
    let e5 : Fin 4 → M := fun i => e4 i.succ
    let e6 : Fin 3 → M := fun i => e5 i.succ
    let e7 : Fin 2 → M := fun i => e6 i.succ
    let x1 := F ones ![e 0+1,l+l]
    let x2 := F ones ![e1 0+1,x1+x1]
    let x3 := F ones ![e2 0+1,x2+x2]
    let x4 := F ones ![e3 0+1,x3+x3]
    let x5 := F ones ![e4 0+1,x4+x4]
    let x6 := F ones ![e5 0+1,x5+x5]
    let x7 := F ones ![e6 0+1,x6+x6]
    let c1 := (1 : M)+(e 0+1)
    let c2 := (1 : M)+(e1 0+1)
    let c3 := (1 : M)+(e2 0+1)
    let c4 := (1 : M)+(e3 0+1)
    let c5 := (1 : M)+(e4 0+1)
    let c6 := (1 : M)+(e5 0+1)
    let c7 := (1 : M)+(e6 0+1)
    F PA194Stepper.stepper ![((((((c1+c2)+c3)+c4)+c5)+c6)+c7),F pairCode ![modelNumeral M 3,
      F pairCode ![l,F ones ![e 0+1,F (fileCode 7) e1]]]] =
    F pairCode ![modelNumeral M 3,F pairCode ![x7,F ones ![e7 0+1,e7 1]]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let e1 : Fin 8 → M := fun i => e i.succ
  let e2 : Fin 7 → M := fun i => e1 i.succ
  let e3 : Fin 6 → M := fun i => e2 i.succ
  let e4 : Fin 5 → M := fun i => e3 i.succ
  let e5 : Fin 4 → M := fun i => e4 i.succ
  let e6 : Fin 3 → M := fun i => e5 i.succ
  let e7 : Fin 2 → M := fun i => e6 i.succ
  let x1 := F ones ![e 0+1,l+l]
  let x2 := F ones ![e1 0+1,x1+x1]
  let x3 := F ones ![e2 0+1,x2+x2]
  let x4 := F ones ![e3 0+1,x3+x3]
  let x5 := F ones ![e4 0+1,x4+x4]
  let x6 := F ones ![e5 0+1,x5+x5]
  let x7 := F ones ![e6 0+1,x6+x6]
  let c1 := (1 : M)+(e 0+1)
  let c2 := (1 : M)+(e1 0+1)
  let c3 := (1 : M)+(e2 0+1)
  let c4 := (1 : M)+(e3 0+1)
  let c5 := (1 : M)+(e4 0+1)
  let c6 := (1 : M)+(e5 0+1)
  let c7 := (1 : M)+(e6 0+1)
  have h1 := carryCell (M := M) (e 0) l (F ones ![e1 0+1,F (fileCode 6) (fun i => e1 i.succ)])
  have hf1 : F (fileCode 7) e1 = (F ones ![e1 0+1,F (fileCode 6) (fun i => e1 i.succ)])+(F ones ![e1 0+1,F (fileCode 6) (fun i => e1 i.succ)]) := by
    rw [modelFileSucc,modelBlock]
  rw [←hf1] at h1
  have h2 := carryCell (M := M) (e1 0) x1 (F ones ![e2 0+1,F (fileCode 5) (fun i => e2 i.succ)])
  have hf2 : F (fileCode 6) e2 = (F ones ![e2 0+1,F (fileCode 5) (fun i => e2 i.succ)])+(F ones ![e2 0+1,F (fileCode 5) (fun i => e2 i.succ)]) := by
    rw [modelFileSucc,modelBlock]
  rw [←hf2] at h2
  have h3 := carryCell (M := M) (e2 0) x2 (F ones ![e3 0+1,F (fileCode 4) (fun i => e3 i.succ)])
  have hf3 : F (fileCode 5) e3 = (F ones ![e3 0+1,F (fileCode 4) (fun i => e3 i.succ)])+(F ones ![e3 0+1,F (fileCode 4) (fun i => e3 i.succ)]) := by
    rw [modelFileSucc,modelBlock]
  rw [←hf3] at h3
  have h4 := carryCell (M := M) (e3 0) x3 (F ones ![e4 0+1,F (fileCode 3) (fun i => e4 i.succ)])
  have hf4 : F (fileCode 4) e4 = (F ones ![e4 0+1,F (fileCode 3) (fun i => e4 i.succ)])+(F ones ![e4 0+1,F (fileCode 3) (fun i => e4 i.succ)]) := by
    rw [modelFileSucc,modelBlock]
  rw [←hf4] at h4
  have h5 := carryCell (M := M) (e4 0) x4 (F ones ![e5 0+1,F (fileCode 2) (fun i => e5 i.succ)])
  have hf5 : F (fileCode 3) e5 = (F ones ![e5 0+1,F (fileCode 2) (fun i => e5 i.succ)])+(F ones ![e5 0+1,F (fileCode 2) (fun i => e5 i.succ)]) := by
    rw [modelFileSucc,modelBlock]
  rw [←hf5] at h5
  have h6 := carryCell (M := M) (e5 0) x5 (F ones ![e6 0+1,F (fileCode 1) (fun i => e6 i.succ)])
  have hf6 : F (fileCode 2) e6 = (F ones ![e6 0+1,F (fileCode 1) (fun i => e6 i.succ)])+(F ones ![e6 0+1,F (fileCode 1) (fun i => e6 i.succ)]) := by
    rw [modelFileSucc,modelBlock]
  rw [←hf6] at h6
  have h7 := carryCell (M := M) (e6 0) x6 (F ones ![e7 0+1,e7 1])
  have hf7 : F (fileCode 1) e7 = (F ones ![e7 0+1,e7 1])+(F ones ![e7 0+1,e7 1]) := by
    rw [modelFileSucc,modelBlock]
    change (F ones ![e7 0+1,F (fileCode 0) (fun i => e7 i.succ)]) + _ = _
    rw [show fileCode 0 = .proj 0 from rfl,modelProjection]
    rfl
  rw [←hf7] at h7
  change F PA194Stepper.stepper ![F addCode ![(((((c1+c2)+c3)+c4)+c5)+c6),c7],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![c7,F PA194Stepper.stepper ![F addCode ![((((c1+c2)+c3)+c4)+c5),c6],_]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![c7,F PA194Stepper.stepper ![c6,F PA194Stepper.stepper ![F addCode ![(((c1+c2)+c3)+c4),c5],_]]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![c7,F PA194Stepper.stepper ![c6,F PA194Stepper.stepper ![c5,F PA194Stepper.stepper ![F addCode ![((c1+c2)+c3),c4],_]]]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![c7,F PA194Stepper.stepper ![c6,F PA194Stepper.stepper ![c5,F PA194Stepper.stepper ![c4,F PA194Stepper.stepper ![F addCode ![(c1+c2),c3],_]]]]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![c7,F PA194Stepper.stepper ![c6,F PA194Stepper.stepper ![c5,F PA194Stepper.stepper ![c4,F PA194Stepper.stepper ![c3,F PA194Stepper.stepper ![F addCode ![c1,c2],_]]]]]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  rw [h1,h2,h3,h4,h5,h6,h7]
#print axioms carrySeven
#print axioms carryCell
end models
end PA194Site28CarrySeven
