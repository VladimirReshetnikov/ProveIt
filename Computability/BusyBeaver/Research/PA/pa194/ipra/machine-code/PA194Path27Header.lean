import PA194ZeroOutputFile
import PA194ZeroRuns
import PA194SourceProgram
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Path27Header
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns
open PA194ZeroOutputFile PRAModelIOpenPairing TableDispatch

theorem path27 : PA194SourceProgram.path 27 = [true,false,false,false,true,false,false] := by
  decide +kernel
#print axioms path27

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- A fixed standard bit prefix interpreted as a model-valued little-endian word. -/
def modelWord : List Bool → M → M
  | [], x => x
  | b::bs, x => let y := modelWord bs x; if b then y+y+1 else y+y

theorem path27Word (z : M) :
    let r := (z+z)+(z+z)
    let t := (1 : M)+r+r
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    modelWord (PA194SourceProgram.path 27) z = t4+1 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  rw [path27]
  simp only [modelWord, Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false]
  simp only [add_assoc,add_comm,add_left_comm]

/-- The output of the zero branch is the exact path-27 bit prefix followed by
    a model-length zero run, delimiter and complete unchanged source file. -/
theorem zeroResultIsPath27 (k : M) (args : Fin 11 → M) (hz : args 8 = (0 : M)) :
    let v := physicalArgs args
    let v1 : Fin 10 → M := fun i => v i.succ
    let rem : Fin 9 → M := fun i => v1 i.succ
    let r := F ones ![rem 0,F (fileCode 7) (fun i => rem i.succ)]
    let p := r+r+1
    let u := p+p
    let file := (u+u+1)+(u+u+1)
    let out := F ones ![v 0,file]
    let q := out+out+1
    let z := F zeros ![k+1,(1 : M)+(q+q)+(q+q)]
    let rr := (z+z)+(z+z)
    let t := (1 : M)+rr+rr
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    t4+1 = modelWord (PA194SourceProgram.path 27)
      (F zeros ![k+1,(1 : M)+(F sourceFileCode args+F sourceFileCode args)]) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let v := physicalArgs args
  let v1 : Fin 10 → M := fun i => v i.succ
  let rem : Fin 9 → M := fun i => v1 i.succ
  let r := F ones ![rem 0,F (fileCode 7) (fun i => rem i.succ)]
  let p := r+r+1
  let u := p+p
  let file := (u+u+1)+(u+u+1)
  let out := F ones ![v 0,file]
  let q := out+out+1
  let f := F sourceFileCode args
  let z := F zeros ![k+1,(1 : M)+(q+q)+(q+q)]
  let rr := (z+z)+(z+z)
  let t := (1 : M)+rr+rr
  let t1 := t+t
  let t2 := t1+t1
  let t3 := t2+t2
  let t4 := t3+t3
  change t4+1 = modelWord (PA194SourceProgram.path 27) (F zeros ![k+1,(1 : M)+(f+f)])
  have hf : f = q+q := by
    have h := sourceFileAfterZero args hz
    dsimp only at h
    change f = ((out+out)+(out+out))+1+1 at h
    rw [h]
    dsimp only [q]
    simp only [add_assoc,add_comm,add_left_comm]
  rw [hf]
  have harg : (1 : M)+(q+q)+(q+q) = 1+((q+q)+(q+q)) := add_assoc _ _ _
  rw [←harg]
  change t4+1 = modelWord (PA194SourceProgram.path 27) z
  exact (path27Word z).symm
#print axioms path27Word
#print axioms zeroResultIsPath27
end models
end PA194Path27Header
