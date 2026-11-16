import PA194AX11HWindowPair
import PA194AX11HWindowTransfer
import PA194ModelMPPush

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace PA194WindowPush
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194ModelMPTransfer PA194ModelMPPush
open PA194WindowTransfer PA194WindowDrain

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

/-- The push executes under any code that agrees on the window containing its rows. -/
theorem push (code : Code 1) (lower bound base : Nat)
    (hagrees : AgreesWindow (M := M) code lower bound) (hbase : lower ≤ base) (hend : base+18 < bound)
    (rows : PA194ModelMPPush.Rows base) (a : Fin 11 → M) (tail : M) (hX : a 6 = 0) (hY : a 7 = 0) :
    PA194PausedReach.Reaches code (sourceState base a tail) (sourceState (base+19) (pushed a) tail) := by
  let a1 := transferArgs a 1 6
  let a2 := transferArgs a1 2 1
  let a3 := PA194ModelMPPair.values a2 0 0 (cantor (a2 6) (a2 1))
  have h1 := PA194WindowTransfer.transfer code lower bound base (base+3) 1 6 hagrees rows.takeTop hbase (by omega) (by decide) a tail
  have h2 := PA194WindowTransfer.transfer code lower bound (base+3) (base+6) 2 1 hagrees rows.takeStack (by omega) (by omega) (by decide) a1 tail
  have hY' : a2 7 = (0 : M) := by simp [a2,a1,transferArgs,location,hY]
  have h3 := PA194WindowPair.pair code lower bound (base+6) hagrees (by omega) (by omega) rows.packPair a2 tail hY'
  have h4 := PA194WindowTransfer.transfer code lower bound (base+16) (base+19) 7 2 hagrees rows.storeStack (by omega) (by omega) (by decide) a3 tail
  have hout : transferArgs a3 7 2 = pushed a := by
    funext i
    fin_cases i <;> simp [a3,a2,a1,transferArgs,location,PA194ModelMPPair.values,pushed,hX,hY]
  rw [hout] at h4
  exact PA194PausedReach.append code (PA194PausedReach.append code (PA194PausedReach.append code h1 h2) h3) h4

#print axioms push
end models
end PA194WindowPush
