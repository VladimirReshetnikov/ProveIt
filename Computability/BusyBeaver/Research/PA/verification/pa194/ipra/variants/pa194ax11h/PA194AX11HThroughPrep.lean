import PA194AX11HPrepExact
import PA194AX11HDoublePushField
import PA194ControllerRunAdd
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HThroughPrep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SchedulerFetchPositive PA194ModelMPPush PA194ModelMPField PA194IteratedSimulation PA194ControllerRunAdd
open PA194AX11HPrepExact
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

/-- The revised AX tail reaches its exact comparison input at site 3642. -/
theorem through_prep (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    ∃ n : M, F (iterate PA194AX11HSource.step) ![n,sourceState 3553 a tail] =
      sourceState 3642 (PA194PausedPrep.result (pushed (fieldArgs (pushed a))) 0 (cantor (a 1) (a 2))) tail := by
  let b := pushed (fieldArgs (pushed a))
  obtain ⟨m,hm⟩ := PA194AX11HDoublePushField.push_field_push a tail hx hy
  obtain ⟨_,h2,_,_,_,h6,h7,_⟩ := PA194AX11HDoublePushField.output_values a
  have hb6 : b 6 = 0 := h6.trans hx
  have hb7 : b 7 = 0 := h7.trans hy
  have hb2 : b 2 = cantor (0 : M) (cantor (a 1) (a 2)) := h2
  obtain ⟨n,hn⟩ := revised_prep_exact b tail 0 (cantor (a 1) (a 2)) hb6 hb7 hb2
  refine ⟨m+n,?_⟩
  rw [iterateAdd,hm,hn]

#print axioms through_prep
end models
end PA194AX11HThroughPrep
