import PA194Site32PositiveTo24
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
namespace PA194Path33Header
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Path27Header PRAModelIOpenPairing

theorem path33 : PA194SourceProgram.path 33 = [true,false,false,false,true,true,true,true] := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem path33Word (z : M) :
    let r := (z+z)+(z+z)
    let r1 := (1 : M)+r+r
    let r2 := r1+r1+1
    let r3 := r2+r2+1
    let t := (1 : M)+r3+r3
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    modelWord (PA194SourceProgram.path 33) r = t4+1 := by
  let r := (z+z)+(z+z)
  let r1 := (1 : M)+r+r
  let r2 := r1+r1+1
  let r3 := r2+r2+1
  let t := (1 : M)+r3+r3
  let t1 := t+t
  let t2 := t1+t1
  let t3 := t2+t2
  let t4 := t3+t3
  have h1 : r+r+1 = r1 := by dsimp only [r1]; ac_rfl
  have h2 : r1+r1+1 = r2 := rfl
  have h3 : r2+r2+1 = r3 := rfl
  have h4 : r3+r3+1 = t := by dsimp only [t]; ac_rfl
  change modelWord (PA194SourceProgram.path 33) r = t4+1
  rw [path33]
  simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false,h1,h2,h3,h4]
  rfl
#print axioms path33
#print axioms path33Word
end models
end PA194Path33Header
