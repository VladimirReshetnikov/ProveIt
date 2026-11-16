import PA194AX11HMPDispatch
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HAXDispatch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194IteratedSimulation
open PA194AX11HSourceAt PA194AX11HMPDispatch
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

/-- AX opcode 2+k takes the two positive decrements and enters the AX body with label k. -/
theorem dispatch (a : Fin 11 → M) (tail k : M) (h : a 3 = k+1+1) :
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 48 a tail)
      (sourceState 50 (Function.update a 3 k) tail) := by
  let b := Function.update a 3 (k+1)
  have h48 := sourceDecPositive 48 49 3 (some 3660) (by decide) row48 a tail (k+1) (by simpa [regsOfArgs] using h)
  have h49 := sourceDecPositive 49 50 3 (some 3572) (by decide) row49 b tail k (by simp [regsOfArgs,b])
  change F PA194AX11HSource.step ![sourceState 48 a tail] = sourceState 49 b tail at h48
  change F PA194AX11HSource.step ![sourceState 49 b tail] = sourceState 50 (Function.update b 3 k) tail at h49
  have he : Function.update b 3 k = Function.update a 3 k := by simp [b,Function.update_idem]
  rw [he] at h49
  exact PA194PausedReach.append _ (PA194PausedReach.oneStep _ h48) (PA194PausedReach.oneStep _ h49)
#print axioms dispatch
end models
end PA194AX11HAXDispatch
