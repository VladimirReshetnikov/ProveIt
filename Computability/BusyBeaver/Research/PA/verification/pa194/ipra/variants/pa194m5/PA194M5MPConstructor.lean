import PA194M5ConsSites
import PA194ModelMPImp

set_option autoImplicit false

namespace PA194M5MPConstructor
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAModelIOpenPairing
open PA194SchedulerFetchPositive
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The final certified radix-five constructor is the sole constructor on the MP branch. -/
theorem build (a : Fin 11 → M) (tail left rest : M) (hx : a 6 = 0) (hy : a 7 = 0)
    (hstack : a 2 = cantor left rest) :
    PA194ProgramDrain.ReachesPositive PA194M5Program.program (sourceState 3654 a tail)
      (sourceState 3682 (PA194ModelMPImp.implicationArgs a
        (PA194ProgramCons.implicationValue 5 left (a 1)) rest) tail) := by
  have houtput : PA194ProgramCons.output 5 a left rest =
      PA194ModelMPImp.implicationArgs a (PA194ProgramCons.implicationValue 5 left (a 1)) rest := by
    funext i
    fin_cases i <;> simp [PA194ProgramCons.output, PA194ModelMPImp.implicationArgs, hx, hy]
  have h := PA194M5ConsSites.constructors (60 : Fin 61) a tail left rest hx hy hstack
  rw [houtput] at h
  exact h

#print axioms build
end models
end PA194M5MPConstructor
