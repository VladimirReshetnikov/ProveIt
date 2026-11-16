import PA194Site27ZeroExact
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27ZeroExactClock
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns
open PRAModelIOpenPairing PA194SourceSite25Physical PA194Site27ZeroExact
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def clock4 (k : M) (e : Fin 11 → M) : M :=
  let v := physicalArgs e
  let f := F sourceFileCode e
  let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  let r := F zeros ![k,f+f+1]
  let s := r+r
  let u0 := s+s
  let u1 := u0+u0
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
  let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
  let w := F ones ![k+1,t]
  let w1 := w+w
  let w2 := w1+w1
  let w3 := w2+w2
  let x := w3+1
  let x1 := x+x
  let x2 := x1+x1
  let x3 := x2+x2
  let x4 := x3+x3
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let rhalf := F ones ![k,t]
  let aa0 := (1 : M)+(1 : M)+1
  let aa1 := aa0+aa0
  let aa2 := aa1+aa1
  let aa3 := aa2+aa2
  let aa4 := aa3+aa3+1
  let aa5 := aa4+aa4
  let aa6 := aa5+aa5
  let n := (k+1)+1
  let a := F ones ![n,aa6+aa6]
  let b := F ones ![k+1,aa6+aa6]
  let base := (b+b+1)+(b+b+1)
  let e0 := v
  let e1 : Fin 10 → M := fun j => e0 j.succ
  let e2 : Fin 9 → M := fun j => e1 j.succ
  let e3 : Fin 8 → M := fun j => e2 j.succ
  let e4 : Fin 7 → M := fun j => e3 j.succ
  let e5 : Fin 6 → M := fun j => e4 j.succ
  let e6 : Fin 5 → M := fun j => e5 j.succ
  let t1 := (e0 0+1)+1
  let t2 := (e1 0+1)+1
  let t3 := (e2 0+1)+1
  let t4 := (e3 0+1)+1
  let t5 := (e4 0+1)+1
  let t6 := (e5 0+1)+1
  let c6 := (((((t1+t2)+t3)+t4)+t5)+t6)
  let q := F ones ![e6 0,F (fileCode 3) (fun i => e6 i.succ)]
  let out := F (fileCode 6) ![v 0,v 1,v 2,v 3,v 4,v 5,(q+q)+(q+q)]
  let rev : Fin 6 → M := ![v 4,v 3,v 2,v 1,v 0,base]
  let cr := (modelNumeral M 2+((v 5+1)+1))+F (PA194CarryFile.costCode 5) rev
  let qf := out+out+1
  let w := F ones ![k+1,qf]
  let w1 := w+w
  let w2 := w1+w1
  let w3 := w2+w2
  let z := (1 : M)+w3+w3
  let z1 := z+z
  let z2 := z1+z1
  let z3 := z2+z2
  let z4 := z3+z3
  let croot := (((((1 : M)+k)+1)+1)+(modelNumeral M 3+(modelNumeral M 3+rc)))
  let vec : Fin 7 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,(q+q)+(q+q)]
  let before := F ones ![k+1,(aa6+aa6)+(aa6+aa6)]
  let carried := F (PA194CarryFile.leftCode 6) (Fin.cases before vec)
  let selectedLeft := carried+carried+1
  let ccarry := ((k+1)+F (PA194CarryFile.costCode 6) vec)+modelNumeral M 2
  let clock := (((((((modelNumeral M 13+(((((k+1)+1)+1)+1)+((k+1)+1)))+(modelNumeral M 5+rc))+modelNumeral M 8)+(n+1))+(c6+cr))+croot)+modelNumeral M 13)+ccarry
  clock

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
    F PA194Stepper.stepper ![F addCode ![clock4 k e,modelNumeral M 1],physicalFrame 27 ((k+1)+1) e] =
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
  have hstart : F PA194Stepper.stepper ![clock4 k e,physicalFrame 27 ((k+1)+1) e] =
      F pairCode ![modelNumeral M 4,F pairCode ![z+z,F ones ![(0 : M),t+t]]] := by
    dsimp only [clock4]
    rw [hq]
    exact h
  have hrow := PA194Site27BranchRows.zeroRow z t
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
    F PA194Stepper.stepper ![F addCode ![F addCode ![clock4 k e,modelNumeral M 1],modelNumeral M 2],physicalFrame 27 ((k+1)+1) e] =
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
  have h5 := zeroTo5Exact k e hz
  dsimp only at h5
  let z := selectedCarry k e + selectedCarry k e + 1
  have h11 := PA194Site27ZeroTo11.fiveTo11 z u
  dsimp only at h11
  rw [←ht] at h11
  rw [PA194StepperCompose.modelStepperCompose,h5]
  exact h11

#print axioms zeroTo5Exact
#print axioms zeroTo11Exact
end models
end PA194Site27ZeroExactClock
