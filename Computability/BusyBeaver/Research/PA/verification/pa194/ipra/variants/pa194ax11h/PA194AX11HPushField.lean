import PA194AX11HPushExact
import PA194AX11HFieldExact
import PA194ControllerRunAdd
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HPushField
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194ModelMPPush PA194ModelMPField PA194IteratedSimulation
open PA194AX11HPushExact PA194AX11HFieldExact PA194ControllerRunAdd
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

/-- The revised AX tail pushes its gate and enters the MP field reader with the exact resulting file. -/
theorem push_then_field (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    ∃ n : M, F (iterate PA194AX11HSource.step) ![n,sourceState 3553 a tail] =
      sourceState 3586 (fieldArgs (pushed a)) tail := by
  obtain ⟨m,hm⟩ := revised_push_exact a tail hx hy
  have hx' : (pushed a) 6 = 0 := by simp [pushed,hx]
  have hy' : (pushed a) 7 = 0 := by simp [pushed,hy]
  obtain ⟨n,hn⟩ := revised_field_exact (pushed a) tail hx' hy'
  refine ⟨m+n,?_⟩
  rw [iterateAdd,hm,hn]

#print axioms push_then_field
end models
end PA194AX11HPushField
