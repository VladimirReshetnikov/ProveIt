import PA194ProgramCantorPair
import PA194ProgramTransfer
import PA194ModelMPPush

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

namespace PA194ProgramPush
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SchedulerFetchPositive PA194ProgramDrain PA194ProgramTransfer
open PA194ModelMPDrain (location)
open PA194ModelMPTransfer (transferArgs)
open PA194ModelMPPush (pushed)

structure Rows (program : Program) (base : Nat) : Prop where
  takeTop : TransferRows program base (base+3) 1 6
  takeStack : TransferRows program (base+3) (base+6) 2 1
  packPair : PA194ProgramCantorPair.Rows program (base+6)
  storeStack : TransferRows program (base+16) (base+19) 7 2

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

/-- The two PA194 MP pushes share the same literal 19-row instruction pattern. -/
theorem push (program : Program) (base : Nat) (rows : Rows program base) (a : Fin 11 → M) (tail : M)
    (hX : a 6 = 0) (hY : a 7 = 0) :
    ReachesPositive program (sourceState base a tail) (sourceState (base+19) (pushed a) tail) := by
  let a1 := transferArgs a 1 6
  let a2 := transferArgs a1 2 1
  let a3 := PA194ModelMPPair.values a2 0 0 (cantor (a2 6) (a2 1))
  have h1 := transfer program base (base+3) 1 6 rows.takeTop (by decide) a tail
  have h2 := transfer program (base+3) (base+6) 2 1 rows.takeStack (by decide) a1 tail
  have hY' : a2 7 = (0 : M) := by simp [a2,a1,transferArgs,location,hY]
  have h3 := PA194ProgramCantorPair.pair program (base+6) rows.packPair a2 tail hY'
  have h4 := transfer program (base+16) (base+19) 7 2 rows.storeStack (by decide) a3 tail
  have hout : transferArgs a3 7 2 = pushed a := by
    funext i
    fin_cases i <;> simp [a3,a2,a1,transferArgs,location,PA194ModelMPPair.values,pushed,hX,hY]
  rw [hout] at h4
  exact appendPositive program (append program (append program h1.reaches h2.reaches) h3.reaches) h4

#print axioms push
end models
end PA194ProgramPush
