import PA194Site27ZeroTo11
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27ZeroExact
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns
open PRAModelIOpenPairing PA194SourceSite25Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def selectedCarry (k : M) (e : Fin 11 → M) : M :=
  let v := physicalArgs e
  let e1 : Fin 10 → M := fun j => v j.succ
  let e2 : Fin 9 → M := fun j => e1 j.succ
  let e3 : Fin 8 → M := fun j => e2 j.succ
  let e4 : Fin 7 → M := fun j => e3 j.succ
  let e5 : Fin 6 → M := fun j => e4 j.succ
  let e6 : Fin 5 → M := fun j => e5 j.succ
  let t := F ones ![e6 1+1,F (fileCode 2) (fun i => e6 i.succ.succ)]
  let q := F ones ![(0 : M),t+t]
  let aa0 := (1 : M)+(1 : M)+1
  let aa1 := aa0+aa0
  let aa2 := aa1+aa1
  let aa3 := aa2+aa2
  let aa4 := aa3+aa3+1
  let aa5 := aa4+aa4
  let aa6 := aa5+aa5
  let before := F ones ![k+1,(aa6+aa6)+(aa6+aa6)]
  let vec : Fin 7 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,(q+q)+(q+q)]
  F (PA194CarryFile.leftCode 6) (Fin.cases before vec)

theorem zeroTo5Exact (k : M) (e : Fin 11 → M) (hz : e 0 = (0 : M)) :
    let v := physicalArgs e
    let e1 : Fin 10 → M := fun j => v j.succ
    let e2 : Fin 9 → M := fun j => e1 j.succ
    let e3 : Fin 8 → M := fun j => e2 j.succ
    let e4 : Fin 7 → M := fun j => e3 j.succ
    let e5 : Fin 6 → M := fun j => e4 j.succ
    let e6 : Fin 5 → M := fun j => e5 j.succ
    let t := F ones ![e6 1+1,F (fileCode 2) (fun i => e6 i.succ.succ)]
    let z := selectedCarry k e + selectedCarry k e + 1
    ∃ clock : M, F PA194Stepper.stepper ![clock,physicalFrame 27 ((k+1)+1) e] =
        F pairCode ![modelNumeral M 5,F pairCode ![(z+z)+(z+z)+1,t]] := by
  dsimp only
  let v := physicalArgs e
  let e1 : Fin 10 → M := fun j => v j.succ
  let e2 : Fin 9 → M := fun j => e1 j.succ
  let e3 : Fin 8 → M := fun j => e2 j.succ
  let e4 : Fin 7 → M := fun j => e3 j.succ
  let e5 : Fin 6 → M := fun j => e4 j.succ
  let e6 : Fin 5 → M := fun j => e5 j.succ
  let t := F ones ![e6 1+1,F (fileCode 2) (fun i => e6 i.succ.succ)]
  have hz' : e6 0 = (0 : M) := hz
  have ht : F (fileCode 3) (fun i => e6 i.succ) = t+t := by
    rw [modelFileSucc,modelBlock]
    rfl
  have hq : F ones ![e6 0,F (fileCode 3) (fun i => e6 i.succ)] = F ones ![(0 : M),t+t] := by
    rw [hz',ht]
  have hin := PA194Path27Input.site27Input k (F sourceFileCode e)
  dsimp only at hin
  have h := PA194Site27To4.site27To4 k e
  dsimp only at h
  rw [hq,hin] at h
  let z := selectedCarry k e + selectedCarry k e + 1
  obtain ⟨clock,hstart⟩ : ∃ clock : M,
      F PA194Stepper.stepper ![clock,physicalFrame 27 ((k+1)+1) e] =
        F pairCode ![modelNumeral M 4,F pairCode ![z+z,F ones ![(0 : M),t+t]]] := by
    exact ⟨_,h⟩
  have hrow := PA194Site27BranchRows.zeroRow z t
  refine ⟨F addCode ![clock,modelNumeral M 1],?_⟩
  rw [PA194StepperCompose.modelStepperCompose,hstart]
  exact hrow
theorem zeroTo11Exact (k : M) (e : Fin 11 → M) (hz : e 0 = (0 : M)) :
    let v := physicalArgs e
    let e1 : Fin 10 → M := fun j => v j.succ
    let e2 : Fin 9 → M := fun j => e1 j.succ
    let e3 : Fin 8 → M := fun j => e2 j.succ
    let e4 : Fin 7 → M := fun j => e3 j.succ
    let e5 : Fin 6 → M := fun j => e4 j.succ
    let e6 : Fin 5 → M := fun j => e5 j.succ
    let t := F ones ![e6 1+1,F (fileCode 2) (fun i => e6 i.succ.succ)]
    let z := selectedCarry k e + selectedCarry k e + 1
    ∃ clock : M, F PA194Stepper.stepper ![clock,physicalFrame 27 ((k+1)+1) e] =
      F pairCode ![modelNumeral M 11,F pairCode ![z,(t+t)+(t+t)]] := by
  dsimp only
  let v := physicalArgs e
  let e1 : Fin 10 → M := fun j => v j.succ
  let e2 : Fin 9 → M := fun j => e1 j.succ
  let e3 : Fin 8 → M := fun j => e2 j.succ
  let e4 : Fin 7 → M := fun j => e3 j.succ
  let e5 : Fin 6 → M := fun j => e4 j.succ
  let e6 : Fin 5 → M := fun j => e5 j.succ
  let t := F ones ![e6 1+1,F (fileCode 2) (fun i => e6 i.succ.succ)]
  let u := F ones ![e6 1,F (fileCode 2) (fun i => e6 i.succ.succ)]
  have ht : t = u+u+1 := by
    dsimp only [t,u]
    rw [show e6 1+1 = F Code.succ (fun _ => e6 1) from modelAddOne _,modelOnesSucc]
  obtain ⟨clock,h5⟩ := zeroTo5Exact k e hz
  dsimp only at h5
  let z := selectedCarry k e + selectedCarry k e + 1
  have h11 := PA194Site27ZeroTo11.fiveTo11 z u
  dsimp only at h11
  rw [←ht] at h11
  refine ⟨F addCode ![clock,modelNumeral M 2],?_⟩
  rw [PA194StepperCompose.modelStepperCompose,h5]
  exact h11
#print axioms zeroTo11Exact
#print axioms zeroTo5Exact
end models
end PA194Site27ZeroExact
