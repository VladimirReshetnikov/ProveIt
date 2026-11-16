import PA194PausedReach
import PA194AX11HPushPaused
import PA194AX11HFieldPaused

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace PA194PausedSites
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourcePCBound
open PA194StateOne PA194PausedReach

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_pc (site : Nat) (a : Fin 11 → M) (tail : M) :
    F pc ![sourceState site a tail] = modelNumeral M site := by
  rw [pcModel]
  exact pi₁_pair _ _

/-- At each site before the push exit, the paused primary step is the actual step. -/
theorem push_step_before (site : Nat) (hsite : site < 3587) (a : Fin 11 → M) (tail : M) :
    F PA194AX11HPushPaused.oldPaused ![sourceState site a tail] =
      F step ![sourceState site a tail] := by
  rw [PA194AX11HPushPaused.oldPaused_model,source_pc]
  exact if_neg (ne_of_lt (modelNumeralStrict site 3587 hsite))

/-- At each site before the field exit, the paused primary step is the actual step. -/
theorem field_step_before (site : Nat) (hsite : site < 3568) (a : Fin 11 → M) (tail : M) :
    F PA194AX11HFieldPaused.oldPaused ![sourceState site a tail] =
      F step ![sourceState site a tail] := by
  rw [PA194AX11HFieldPaused.oldPaused_model,source_pc]
  exact if_neg (ne_of_lt (modelNumeralStrict site 3568 hsite))

theorem push_exit_stable (a : Fin 11 → M) (tail : M) :
    F PA194AX11HPushPaused.oldPaused ![sourceState 3587 a tail] = sourceState 3587 a tail := by
  rw [PA194AX11HPushPaused.oldPaused_model,source_pc,if_pos rfl]

theorem field_exit_stable (a : Fin 11 → M) (tail : M) :
    F PA194AX11HFieldPaused.oldPaused ![sourceState 3568 a tail] = sourceState 3568 a tail := by
  rw [PA194AX11HFieldPaused.oldPaused_model,source_pc,if_pos rfl]

theorem push_one_step (site : Nat) (hsite : site < 3587) (a : Fin 11 → M) (tail target : M)
    (h : F step ![sourceState site a tail] = target) :
    Reaches PA194AX11HPushPaused.oldPaused (sourceState site a tail) target := by
  apply PA194PausedReach.oneStep
  rw [push_step_before site hsite a tail,h]

theorem field_one_step (site : Nat) (hsite : site < 3568) (a : Fin 11 → M) (tail target : M)
    (h : F step ![sourceState site a tail] = target) :
    Reaches PA194AX11HFieldPaused.oldPaused (sourceState site a tail) target := by
  apply PA194PausedReach.oneStep
  rw [field_step_before site hsite a tail,h]

#print axioms push_step_before
#print axioms field_step_before
#print axioms push_exit_stable
#print axioms field_exit_stable
#print axioms push_one_step
#print axioms field_one_step
end models
end PA194PausedSites
