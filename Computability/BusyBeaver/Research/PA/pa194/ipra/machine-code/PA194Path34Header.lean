import PA194Site32ZeroTo24
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace PA194Path34Header
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Path27Header PRAModelIOpenPairing

theorem path34 : PA194SourceProgram.path 34 = [true,false,false,true,false,false,false] := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem path34Word (z : M) :
    let d := z+z
    let r := (d+d)+(d+d)
    let s := (1+1)+(r+r)+(r+r)
    modelWord (PA194SourceProgram.path 34) z = (s+s)+(s+s)+1 := by
  dsimp only
  rw [path34]
  simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false]
  ac_rfl
#print axioms path34
#print axioms path34Word
end models
end PA194Path34Header
