import Mathlib.Tactic.Ring
import PA194Path27Header
import PA194Site27PositiveFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Path28Header
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns
open PA194Site27PositiveFile PA194Path27Header PRAModelIOpenPairing TableDispatch

theorem path28 : PA194SourceProgram.path 28 = [true,false,false,false,true,false,true,false] := by
  decide +kernel
#print axioms path28
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem path28Word (z : M) :
    let r := (z+z)+(z+z)
    let x := (1+1)+(r+r)+(r+r)
    let t := (1 : M)+x+x
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    modelWord (PA194SourceProgram.path 28) (z+z) = t4+1 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let z1 := z+z
  let z2 := z1+z1
  let z3 := z2+z2+1
  let z4 := z3+z3
  let stem := z4+z4+1
  let r := (z+z)+(z+z)
  let x := (1+1)+(r+r)+(r+r)
  let t := (1 : M)+x+x
  let t1 := t+t
  let t2 := t1+t1
  let t3 := t2+t2
  let t4 := t3+t3
  let p1 := stem+stem
  let p2 := p1+p1
  let p3 := p2+p2
  let p4 := p3+p3
  have he : stem=t := by
    dsimp only [stem,z4,z3,z2,z1,t,x,r]
    ring
  rw [path28]
  change p4+1=t4+1
  dsimp only [p4,p3,p2,p1]
  rw [he]

theorem positiveResultIsPath28 (k m : M) (args : Fin 11 → M) :
    let v := physicalArgs args
    let e6 : Fin 5 → M := fun i => v ⟨i.val+6,by omega⟩
    let tail := F (fileCode 3) (fun i => e6 i.succ)
    let rp := F ones ![m,tail]
    let file0 := rp+rp+1
    let f1 := F ones ![v 5,(file0+file0)+(file0+file0)+1]
    let f2 := F ones ![v 4,(f1+f1)+(f1+f1)+1]
    let f3 := F ones ![v 3,(f2+f2)+(f2+f2)+1]
    let f4 := F ones ![v 2,(f3+f3)+(f3+f3)+1]
    let f5 := F ones ![v 1,(f4+f4)+(f4+f4)+1]
    let f6 := F ones ![v 0,(f5+f5)+(f5+f5)+1]
    let z := F zeros ![k+1,(1 : M)+(f6+f6)+(f6+f6)]
    let r := (z+z)+(z+z)
    let x := (1+1)+(r+r)+(r+r)
    let t := (1 : M)+x+x
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    let f := F sourceFileCode (Function.update args 0 m)
    t4+1 = modelWord (PA194SourceProgram.path 28)
      (F zeros ![(k+1)+1,(1 : M)+(f+f)]) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let v := physicalArgs args
  let e6 : Fin 5 → M := fun i => v ⟨i.val+6,by omega⟩
  let tail := F (fileCode 3) (fun i => e6 i.succ)
  let rp := F ones ![m,tail]
  let file0 := rp+rp+1
  let f1 := F ones ![v 5,(file0+file0)+(file0+file0)+1]
  let f2 := F ones ![v 4,(f1+f1)+(f1+f1)+1]
  let f3 := F ones ![v 3,(f2+f2)+(f2+f2)+1]
  let f4 := F ones ![v 2,(f3+f3)+(f3+f3)+1]
  let f5 := F ones ![v 1,(f4+f4)+(f4+f4)+1]
  let f6 := F ones ![v 0,(f5+f5)+(f5+f5)+1]
  let f := F sourceFileCode (Function.update args 0 m)
  let z := F zeros ![k+1,(1 : M)+(f6+f6)+(f6+f6)]
  let r := (z+z)+(z+z)
  let x := (1+1)+(r+r)+(r+r)
  let t := (1 : M)+x+x
  let t1 := t+t
  let t2 := t1+t1
  let t3 := t2+t2
  let t4 := t3+t3
  change t4+1 = modelWord (PA194SourceProgram.path 28) (F zeros ![(k+1)+1,(1 : M)+(f+f)])
  have hf : f=f6+f6 := returnedFile m args
  have harg : (1 : M)+(f+f) = (1 : M)+(f6+f6)+(f6+f6) := by
    rw [hf]
    simp only [add_assoc]
  have hzero : F zeros ![k+1,(1 : M)+(f+f)] = z := by
    exact congrArg (fun a : M => F zeros ![k+1,a]) harg
  have hz : F zeros ![(k+1)+1,(1 : M)+(f+f)] = z+z := by
    rw [show (k+1)+1 = F Code.succ (fun _ => k+1) from modelAddOne _,modelZerosSucc]
    exact congrArg (fun a : M => a+a) hzero
  rw [hz]
  exact (path28Word z).symm
#print axioms path28Word
#print axioms positiveResultIsPath28
end models
end PA194Path28Header
