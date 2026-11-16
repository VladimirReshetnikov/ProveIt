import PA194AX11HPushFieldValues
import PA194AX11HSecondPushExact
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HDoublePushField
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194ModelMPPush PA194ModelMPField PA194IteratedSimulation
open PA194AX11HPushField PA194AX11HPushFieldValues PA194ControllerRunAdd
open PA194MachineProjections
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
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

/-- The revised AX tail runs its inserted push, field reader, and second push
with the exact full source file at site 3605. -/
theorem push_field_push (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    ∃ n : M, F (iterate PA194AX11HSource.step) ![n,sourceState 3553 a tail] =
      sourceState 3605 (pushed (fieldArgs (pushed a))) tail := by
  obtain ⟨m,hm⟩ := push_then_field a tail hx hy
  obtain ⟨_,_,_,h6,h7,_⟩ := output_values a
  have hx' : fieldArgs (pushed a) 6 = 0 := h6.trans hx
  have hy' : fieldArgs (pushed a) 7 = 0 := h7.trans hy
  obtain ⟨n,hn⟩ := PA194AX11HSecondPushExact.revised_push_exact (fieldArgs (pushed a)) tail hx' hy'
  refine ⟨m+n,?_⟩
  rw [iterateAdd,hm,hn]

/-- Coordinate form of the full file presented to the comparison preparation. -/
theorem output_values (a : Fin 11 → M) :
    pushed (fieldArgs (pushed a)) 1 = 0 ∧
    pushed (fieldArgs (pushed a)) 2 = cantor (0 : M) (cantor (a 1) (a 2)) ∧
    pushed (fieldArgs (pushed a)) 3 = a 3 ∧
    pushed (fieldArgs (pushed a)) 4 = a 4 + F fixedFirst ![a 8] ∧
    pushed (fieldArgs (pushed a)) 5 = a 5 ∧
    pushed (fieldArgs (pushed a)) 6 = a 6 ∧
    pushed (fieldArgs (pushed a)) 7 = a 7 ∧
    pushed (fieldArgs (pushed a)) 8 = F fixedSecond ![a 8] := by
  simp [fieldArgs,pushed]

#print axioms output_values
#print axioms push_field_push
end models
end PA194AX11HDoublePushField
