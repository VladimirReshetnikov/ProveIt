import Mathlib.Tactic.FinCases
import PA194RegisterPermutation
import PA194ReturnFileMeaning
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site48PositiveFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ReturnFileMeaning PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem returnedFile (m : M) (args : Fin 11 → M) :
    let v := physicalArgs args
    let e4 : Fin 7 → M := fun i => v ⟨i.val+4,by omega⟩
    let tail := F (fileCode 5) (fun i => e4 i.succ)
    let rp := F ones ![m,tail]
    let file0 := rp+rp+1
    let f1 := F ones ![v 3,(file0+file0)+(file0+file0)+1]
    let f2 := F ones ![v 2,(f1+f1)+(f1+f1)+1]
    let f3 := F ones ![v 1,(f2+f2)+(f2+f2)+1]
    let f4 := F ones ![v 0,(f3+f3)+(f3+f3)+1]
    F sourceFileCode (Function.update args 3 m) = f4+f4 := by
  classical
  dsimp only
  let v := physicalArgs args
  let e4 : Fin 7 → M := fun i => v ⟨i.val+4,by omega⟩
  let tail := F (fileCode 5) (fun i => e4 i.succ)
  let rp := F ones ![m,tail]
  let file0 := rp+rp+1
  let f1 := F ones ![v 3,(file0+file0)+(file0+file0)+1]
  let f2 := F ones ![v 2,(f1+f1)+(f1+f1)+1]
  let f3 := F ones ![v 1,(f2+f2)+(f2+f2)+1]
  let f4 := F ones ![v 0,(f3+f3)+(f3+f3)+1]
  let t0 := F block ![m,tail]
  let t1 := F block ![v 3,t0]
  let t2 := F block ![v 2,t1]
  let t3 := F block ![v 1,t2]
  let t4 := F block ![v 0,t3]
  have hv : physicalArgs (Function.update args 3 m) = Function.update v 4 m := by
    funext i
    fin_cases i <;> rfl
  have h0 : t0=file0+file0 := by
    dsimp only [t0,file0]
    rw [modelBlock]
    change F ones ![F addCode ![m,F oneCode Fin.elim0],tail] + F ones ![F addCode ![m,F oneCode Fin.elim0],tail] = _
    rw [modelAddOne,modelOnesSucc]
  have hnext (v' x y : M) (hy : y=x+x) :
      F block ![v',y] = (F ones ![v',(x+x)+(x+x)+1])+(F ones ![v',(x+x)+(x+x)+1]) := by
    rw [hy]
    exact (modelReturnBlock v' (x+x)).symm
  have h1 : t1=f1+f1 := hnext (v 3) file0 t0 h0
  have h2 : t2=f2+f2 := hnext (v 2) f1 t1 h1
  have h3 : t3=f3+f3 := hnext (v 1) f2 t2 h2
  have h4 : t4=f4+f4 := hnext (v 0) f3 t3 h3
  have hf : F sourceFileCode (Function.update args 3 m) = t4 := by
    rw [modelSourceFile,hv]
    rw [modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc]
    rfl
  change F sourceFileCode (Function.update args 3 m) = f4+f4
  rw [hf,h4]
#print axioms returnedFile
end models
end PA194Site48PositiveFile
