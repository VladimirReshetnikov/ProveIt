import PA194AX11HInitialOrbit
import PA194StackCode
set_option autoImplicit false
namespace PA194AX11HDropOrbit
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage
open PA194StackCode PA194IteratedSimulation
/-- The scheduler's stack iterator is the source-orbit iterator as a PRA code. -/
theorem iterate_eq_drop (next : Code 1) : iterate next = dropCode next := by
  rfl
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRATheory PRAAddOne PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SchedulerIteration PA194AX11HSourceOrbit
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
theorem site10_iff_drop_scheduler (next flag : Code 1)
    (returning : ∀ s : M, F flag ![s] ≠ 1 →
      ∃ c : M, 0 < c ∧ F sourceRun ![c,F PA194SchedulerSourceFrame.frame ![s]] =
        F PA194SchedulerSourceFrame.frame ![F next ![s]])
    (halting : ∀ s : M, F flag ![s] = 1 →
      ∃ c : M, F pc ![F sourceRun ![c,F PA194SchedulerSourceFrame.frame ![s]]] = modelNumeral M 10) :
    (∃ t : M, F pc ![F sourceRun ![t,(PA194CompressedStartup.initialSource : M)]] = modelNumeral M 10) ↔
      ∃ n : M, F flag ![F (dropCode next) ![n,F initial Fin.elim0]] = 1 := by
  simpa only [iterate_eq_drop] using
    (PA194AX11HInitialOrbit.site10_iff_scheduler next flag returning halting)
#print axioms iterate_eq_drop
#print axioms site10_iff_drop_scheduler
end models
end PA194AX11HDropOrbit
