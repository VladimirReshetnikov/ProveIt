import PA194Site28SeedTailRoundTrip
import PA194Site28AfterCarrySeven
import PA194Path28Input
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
namespace PA194Site28SeedRoundTrip
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194ZeroRuns PA194RegisterFile PA194RegisterPermutation PA194Site28SeedTail PA194Site28SeedTailRoundTrip PA194StartupSourceFrame PA194Site28CarryFile PA194Site28CarryCodes PA194UnaryRuns PA194BinaryDouble PA194StateOne PA194CarryFile PA194ReturnFile PRAModelIOpenPairing BinaryTapeCodes
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

def rootClock (k : M) (args : Fin 11 → M) : M :=
    let v := physicalArgs args
    let f := F sourceFileCode args
    let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
    let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
    let r := F ones ![k,t]
    let e : Fin 12 → M := Fin.cases (k+1) v
    let e1 : Fin 11 → M := fun i => e i.succ
    let e2 : Fin 10 → M := fun i => e1 i.succ
    let b := F ones ![e2 0,F (fileCode 8) (fun i => e2 i.succ)]
    let c := (b+b)+(b+b)
    let w1 := F ones ![e1 0,(1 : M)+c+c]
    let w2 := F ones ![e 0,(1 : M)+(w1+w1)+(w1+w1)]
    let scanClock := ((e 0+1)+1)+((e1 0+1)+1)
    let backClock := (e1 0+1)+((e 0+1)+1)
    let s0 := r+r+1
    let z0 := s0+s0
    let z1 := z0+z0+1
    let z2 := z1+z1
    let z3 := z2+z2+1
    let z4 := z3+z3
    let z5 := z4+z4
    let z6 := z5+z5
    let v1 := w2+w2
    let v2 := v1+v1
    let v3 := v2+v2
    let x0 := v3+1
    let x1 := x0+x0
    let x2 := x1+x1+1
    let x3 := x2+x2
    let x4 := x3+x3
    let x5 := x4+x4
    let x6 := x5+x5+1
    let returnClock := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let s := F zeros ![k,f+f+1]
    let t0 := s+s
    let t1 := t0+t0
    let u0 := t1+t1
    let u1 := u0+u0+1
    let u2 := u1+u1
    let u3 := u2+u2+1
    let u4 := u3+u3
    let u5 := u4+u4
    let u6 := u5+u5
    let c0 := modelNumeral M 16+(((((k+1)+1)+1)+1)+((k+1)+1))
    let c1 := (modelNumeral M 4+modelNumeral M 2)+returnClock
    let c2 := ((modelNumeral M 9+((scanClock+modelNumeral M 3)+backClock))+modelNumeral M 7)+returnClock
    let r2 := F ones ![k,(1 : M)+(w1+w1)+(w1+w1)]
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4
    let a6 := a5+a5+1
    let a7 := a6+a6
    let l0 := (a7+a7)+(a7+a7)
    let d0 := F ones ![k,l0]
    let d1 := d0+d0+1
    let d2 := d1+d1
    let d3 := d2+d2+1
    let d4 := F ones ![v 0,d3]
    let scan := ((k+modelNumeral M 2)+(modelNumeral M 1+v 0))+modelNumeral M 2
    let tail := F ones ![e2 1+1,F (fileCode 7) (fun i => e2 (i.succ.succ))]
    let left := (d4+d4)+(d4+d4)+1
    let marked := F ones ![args 8+1,left]
    let rest : Fin 9 → M := fun i => e2 i.succ
    let rest1 : Fin 8 → M := fun i => rest i.succ
    let rest2 : Fin 7 → M := fun i => rest1 i.succ
    let rest3 : Fin 6 → M := fun i => rest2 i.succ
    let rest4 : Fin 5 → M := fun i => rest3 i.succ
    let rest5 : Fin 4 → M := fun i => rest4 i.succ
    let rest6 : Fin 3 → M := fun i => rest5 i.succ
    let rest7 : Fin 2 → M := fun i => rest6 i.succ
    let z1 := F ones ![rest 0+1,marked+marked]
    let z2 := F ones ![rest1 0+1,z1+z1]
    let z3 := F ones ![rest2 0+1,z2+z2]
    let z4 := F ones ![rest3 0+1,z3+z3]
    let z5 := F ones ![rest4 0+1,z4+z4]
    let z6 := F ones ![rest5 0+1,z5+z5]
    let z7 := F ones ![rest6 0+1,z6+z6]
    let j1 := (1 : M)+(rest 0+1)
    let j2 := (1 : M)+(rest1 0+1)
    let j3 := (1 : M)+(rest2 0+1)
    let j4 := (1 : M)+(rest3 0+1)
    let j5 := (1 : M)+(rest4 0+1)
    let j6 := (1 : M)+(rest5 0+1)
    let j7 := (1 : M)+(rest6 0+1)
    let after := ((((((j1+j2)+j3)+j4)+j5)+j6)+j7)
    let prior := ((((c0+c1)+c2)+modelNumeral M 16)+scan)+(args 8+1)
    prior+after

def marked (k : M) (args : Fin 11 → M) : M :=
    let v := physicalArgs args
    let f := F sourceFileCode args
    let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
    let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
    let r := F ones ![k,t]
    let e : Fin 12 → M := Fin.cases (k+1) v
    let e1 : Fin 11 → M := fun i => e i.succ
    let e2 : Fin 10 → M := fun i => e1 i.succ
    let b := F ones ![e2 0,F (fileCode 8) (fun i => e2 i.succ)]
    let c := (b+b)+(b+b)
    let w1 := F ones ![e1 0,(1 : M)+c+c]
    let w2 := F ones ![e 0,(1 : M)+(w1+w1)+(w1+w1)]
    let scanClock := ((e 0+1)+1)+((e1 0+1)+1)
    let backClock := (e1 0+1)+((e 0+1)+1)
    let s0 := r+r+1
    let z0 := s0+s0
    let z1 := z0+z0+1
    let z2 := z1+z1
    let z3 := z2+z2+1
    let z4 := z3+z3
    let z5 := z4+z4
    let z6 := z5+z5
    let v1 := w2+w2
    let v2 := v1+v1
    let v3 := v2+v2
    let x0 := v3+1
    let x1 := x0+x0
    let x2 := x1+x1+1
    let x3 := x2+x2
    let x4 := x3+x3
    let x5 := x4+x4
    let x6 := x5+x5+1
    let returnClock := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let s := F zeros ![k,f+f+1]
    let t0 := s+s
    let t1 := t0+t0
    let u0 := t1+t1
    let u1 := u0+u0+1
    let u2 := u1+u1
    let u3 := u2+u2+1
    let u4 := u3+u3
    let u5 := u4+u4
    let u6 := u5+u5
    let c0 := modelNumeral M 16+(((((k+1)+1)+1)+1)+((k+1)+1))
    let c1 := (modelNumeral M 4+modelNumeral M 2)+returnClock
    let c2 := ((modelNumeral M 9+((scanClock+modelNumeral M 3)+backClock))+modelNumeral M 7)+returnClock
    let r2 := F ones ![k,(1 : M)+(w1+w1)+(w1+w1)]
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4
    let a6 := a5+a5+1
    let a7 := a6+a6
    let l0 := (a7+a7)+(a7+a7)
    let d0 := F ones ![k,l0]
    let d1 := d0+d0+1
    let d2 := d1+d1
    let d3 := d2+d2+1
    let d4 := F ones ![v 0,d3]
    let scan := ((k+modelNumeral M 2)+(modelNumeral M 1+v 0))+modelNumeral M 2
    let tail := F ones ![e2 1+1,F (fileCode 7) (fun i => e2 (i.succ.succ))]
    let left := (d4+d4)+(d4+d4)+1
    let marked := F ones ![args 8+1,left]
    let rest : Fin 9 → M := fun i => e2 i.succ
    let rest1 : Fin 8 → M := fun i => rest i.succ
    let rest2 : Fin 7 → M := fun i => rest1 i.succ
    let rest3 : Fin 6 → M := fun i => rest2 i.succ
    let rest4 : Fin 5 → M := fun i => rest3 i.succ
    let rest5 : Fin 4 → M := fun i => rest4 i.succ
    let rest6 : Fin 3 → M := fun i => rest5 i.succ
    let rest7 : Fin 2 → M := fun i => rest6 i.succ
    let z1 := F ones ![rest 0+1,marked+marked]
    let z2 := F ones ![rest1 0+1,z1+z1]
    let z3 := F ones ![rest2 0+1,z2+z2]
    let z4 := F ones ![rest3 0+1,z3+z3]
    let z5 := F ones ![rest4 0+1,z4+z4]
    let z6 := F ones ![rest5 0+1,z5+z5]
    let z7 := F ones ![rest6 0+1,z6+z6]
    let j1 := (1 : M)+(rest 0+1)
    let j2 := (1 : M)+(rest1 0+1)
    let j3 := (1 : M)+(rest2 0+1)
    let j4 := (1 : M)+(rest3 0+1)
    let j5 := (1 : M)+(rest4 0+1)
    let j6 := (1 : M)+(rest5 0+1)
    let j7 := (1 : M)+(rest6 0+1)
    let after := ((((((j1+j2)+j3)+j4)+j5)+j6)+j7)
    let prior := ((((c0+c1)+c2)+modelNumeral M 16)+scan)+(args 8+1)
    z7

theorem rootToState3 (k : M) (args : Fin 11 → M) :
    let f := F sourceFileCode args
    F PA194Stepper.stepper ![rootClock k args,F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),
      PA194Path27Header.modelWord (PA194SourceProgram.path 28) (F zeros ![(k+1)+1,(1 : M)+(f+f)])]]] =
    F pairCode ![modelNumeral M 3,F pairCode ![marked k args,F ones ![args 9+1,args 10]]] := by
  have h := PA194Site28AfterCarrySeven.afterCarrySeven k args
  have hin := PA194Path28Input.site28Input (M := M) k (F sourceFileCode args)
  dsimp only at h hin ⊢
  rw [←hin]
  exact h

theorem markedOdd (k : M) (args : Fin 11 → M) :
    F parityCode (fun _ => marked k args) = (1 : M) := by
  let v := physicalArgs args
  let e : Fin 12 → M := Fin.cases (k+1) v
  let e1 : Fin 11 → M := fun i => e i.succ
  let e2 : Fin 10 → M := fun i => e1 i.succ
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4
  let a6 := a5+a5+1
  let a7 := a6+a6
  let l0 := (a7+a7)+(a7+a7)
  let d0 := F ones ![k,l0]
  let d1 := d0+d0+1
  let d2 := d1+d1
  let d3 := d2+d2+1
  let d4 := F ones ![v 0,d3]
  let left := (d4+d4)+(d4+d4)+1
  let z0 := F ones ![args 8+1,left]
  let rest : Fin 9 → M := fun i => e2 i.succ
  let rest1 : Fin 8 → M := fun i => rest i.succ
  let rest2 : Fin 7 → M := fun i => rest1 i.succ
  let rest3 : Fin 6 → M := fun i => rest2 i.succ
  let rest4 : Fin 5 → M := fun i => rest3 i.succ
  let rest5 : Fin 4 → M := fun i => rest4 i.succ
  let rest6 : Fin 3 → M := fun i => rest5 i.succ
  let z1 := F ones ![rest 0+1,z0+z0]
  let z2 := F ones ![rest1 0+1,z1+z1]
  let z3 := F ones ![rest2 0+1,z2+z2]
  let z4 := F ones ![rest3 0+1,z3+z3]
  let z5 := F ones ![rest4 0+1,z4+z4]
  let z6 := F ones ![rest5 0+1,z5+z5]
  change F parityCode (fun _ => F ones ![rest6 0+1,z6+z6]) = (1 : M)
  have hs : F ones ![rest6 0+1,z6+z6] = F ones ![rest6 0,z6+z6]+F ones ![rest6 0,z6+z6]+1 := by
    change F ones ![F addCode ![rest6 0,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  rw [hs,(modelOdd _).1]

theorem rootToSeedReturn (k : M) (args : Fin 11 → M)
    (htail : args 10 = modelNumeral M seedTail) :
    let f := F sourceFileCode args
    let e := PA194Site28SeedTailRoundTrip.ext (args 9)
    let v := e ⟨25,by decide⟩
    let l := marked k args
    let s := ((1 : M)+1)+1
    let q := s+s
    let w := F ones ![v,(1 : M)+q+q]
    let t := w+w
    let vals : Fin 26 → M := fun i => e i.castSucc
    let out := F (PA194ReturnFile.returnCode 25) (Fin.cases t vals)
    F PA194Stepper.stepper ![F (PA194CarryFile.costCode 25) vals,
      F PA194Stepper.stepper ![modelNumeral M 2+((v+1)+1),
        F PA194Stepper.stepper ![modelNumeral M 3,
          F PA194Stepper.stepper ![(1 : M)+(v+1),
            F PA194Stepper.stepper ![F (timeCode 25) e,
              F PA194Stepper.stepper ![rootClock k args,F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),
                PA194Path27Header.modelWord (PA194SourceProgram.path 28)
                  (F zeros ![(k+1)+1,(1 : M)+(f+f)])]]]]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),out+out+1]] := by
  let e := PA194Site28SeedTailRoundTrip.ext (args 9)
  let v := e ⟨25,by decide⟩
  let l := marked k args
  let vals : Fin 26 → M := fun i => e i.castSucc
  have hroot := rootToState3 k args
  dsimp only at hroot
  rw [htail] at hroot
  have hret := PA194Site28SeedTailRoundTrip.seedTailRoundTrip (M := M) (args 9) l (markedOdd k args)
  dsimp only at hret
  change F PA194Stepper.stepper ![F (PA194CarryFile.costCode 25) vals,
    F PA194Stepper.stepper ![modelNumeral M 2+((v+1)+1),
      F PA194Stepper.stepper ![modelNumeral M 3,
        F PA194Stepper.stepper ![(1 : M)+(v+1),
          F PA194Stepper.stepper ![F (timeCode 25) e,
            F PA194Stepper.stepper ![rootClock k args,_]]]]]] = _
  rw [hroot,hret]
#print axioms rootToSeedReturn
#print axioms rootToState3
#print axioms markedOdd
end models
end PA194Site28SeedRoundTrip
