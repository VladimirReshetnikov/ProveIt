import PA194AX11HFieldExact
import PA194AX11HSecondPushExact
import PA194AX11HPrepExact
import PA194ControllerRunAdd
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HMPPrep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SchedulerFetchPositive PA194ModelMPPush PA194ModelMPField PA194IteratedSimulation
open PA194ControllerRunAdd
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

/-- Ordinary revised MP: decode its field, save T on the stack, and prepare
its comparison, keeping the full source file and model-valued time. -/
theorem mp_to_compare (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    ∃ n : M, F (iterate PA194AX11HSource.step) ![n,sourceState 3572 a tail] =
      sourceState 3642 (PA194PausedPrep.result (pushed (fieldArgs a)) (a 1) (a 2)) tail := by
  obtain ⟨m,hm⟩ := PA194AX11HFieldExact.revised_field_exact a tail hx hy
  have hx' : fieldArgs a 6 = 0 := by simp [fieldArgs,hx]
  have hy' : fieldArgs a 7 = 0 := by simp [fieldArgs,hy]
  obtain ⟨n,hn⟩ := PA194AX11HSecondPushExact.revised_push_exact (fieldArgs a) tail hx' hy'
  have hx'' : pushed (fieldArgs a) 6 = 0 := by simp [pushed,fieldArgs,hx]
  have hy'' : pushed (fieldArgs a) 7 = 0 := by simp [pushed,fieldArgs,hy]
  have hw : pushed (fieldArgs a) 2 = cantor (a 1) (a 2) := by simp [pushed,fieldArgs]
  obtain ⟨k,hk⟩ := PA194AX11HPrepExact.revised_prep_exact (pushed (fieldArgs a)) tail (a 1) (a 2) hx'' hy'' hw
  refine ⟨(m+n)+k,?_⟩
  rw [iterateAdd,iterateAdd,hm,hn,hk]

#print axioms mp_to_compare
end models
end PA194AX11HMPPrep
