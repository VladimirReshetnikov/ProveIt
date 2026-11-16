import PA194ModelMPDrain
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace PA194ShiftReaderAlgebra
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194ModelMPDrain
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def decoded (args : Fin 11 → M) (x y : M) :=
  Function.update (Function.update (Function.update args (location 2) 0) (location 6) x) (location 7) y

theorem output (args : Fin 11 → M) (x y : M) :
    let a := decoded args x y
    let b := argsAfter a 7 [2] (a 7)
    argsAfter b 6 [5] (b 6) =
      Function.update (Function.update (Function.update (Function.update args 2 y)
        5 (args 5+x)) 6 0) 7 0 := by
  funext i
  fin_cases i <;> simp [decoded, argsAfter, tally, location, subSelf,
    PA194StateOne.modelNumeralOne, show modelNumeral M 0 = (0:M) from rfl]
#print axioms output
end models
end PA194ShiftReaderAlgebra
