import PA194Path27Header
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Path32Header
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194Path27Header PRAModelIOpenPairing

theorem path32 : PA194SourceProgram.path 32 = [true,false,false,false,true,true,true,false] := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem path32Word (z : M) :
    let r := (z+z)+(z+z)
    let r1 := (1 : M)+r+r
    let r2 := r1+r1+1
    let t := (1 : M)+r2+r2
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    modelWord (PA194SourceProgram.path 32) (z+z) = t4+1 := by
  dsimp only
  rw [path32]
  simp only [modelWord, Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false]
  ac_rfl
#print axioms path32
#print axioms path32Word
end models
end PA194Path32Header
