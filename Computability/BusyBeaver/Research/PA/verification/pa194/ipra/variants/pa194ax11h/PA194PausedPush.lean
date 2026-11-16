import PA194PausedPair
import PA194ModelMPPush

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace PA194PausedPush
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194ModelMPTransfer PA194ModelMPPush
open PA194PausedTransfer

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

/-- The primary MP push computes the exact output under the code frozen
at its first exit; no claim about the later actual orbit is required. -/
theorem push (a : Fin 11 → M) (tail : M) (hX : a 6 = 0) (hY : a 7 = 0) :
    PA194PausedReach.Reaches PA194AX11HPushPaused.oldPaused
      (sourceState 3568 a tail) (sourceState 3587 (pushed a) tail) := by
  let code := PA194AX11HPushPaused.oldPaused
  let a1 := transferArgs a 1 6
  let a2 := transferArgs a1 2 1
  let a3 := PA194ModelMPPair.values a2 0 0 (cantor (a2 6) (a2 1))
  have h1 := PA194PausedTransfer.transfer code 3587 3568 3571 1 6 push_agrees entryRows.takeTop (by decide) (by decide) a tail
  have h2 := PA194PausedTransfer.transfer code 3587 3571 3574 2 1 push_agrees entryRows.takeStack (by decide) (by decide) a1 tail
  have hY' : a2 7 = (0 : M) := by simp [a2,a1,transferArgs,location,hY]
  have h3 := PA194PausedPair.pair code 3587 3574 push_agrees (by decide) entryRows.packPair a2 tail hY'
  have h4 := PA194PausedTransfer.transfer code 3587 3584 3587 7 2 push_agrees entryRows.storeStack (by decide) (by decide) a3 tail
  have hout : transferArgs a3 7 2 = pushed a := by
    funext i
    fin_cases i <;> simp [a3,a2,a1,transferArgs,location,PA194ModelMPPair.values,pushed,hX,hY]
  rw [hout] at h4
  exact PA194PausedReach.append code (PA194PausedReach.append code (PA194PausedReach.append code h1 h2) h3) h4

#print axioms push
end models
end PA194PausedPush
