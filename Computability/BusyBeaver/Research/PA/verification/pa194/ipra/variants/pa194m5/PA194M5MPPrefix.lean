import PA194M5MPField
import PA194M5MPPush
import PA194M5MPCopy
import PA194M5MPConstructor
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194M5MPPrefix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194ProgramDrain PA194M5Program
open PA194ModelMPPush (pushed)
open PA194ModelMPField (fieldArgs)
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

noncomputable def beforeConstructor (a : Fin 11 → M) : Fin 11 → M :=
  let b := pushed (fieldArgs a)
  Function.update b 1 (b 1+b 4)

theorem throughConstructor (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    ReachesPositive program (sourceState 3614 a tail)
      (sourceState 3682 (PA194ModelMPImp.implicationArgs (beforeConstructor a)
        (PA194ProgramCons.implicationValue 5 (a 1) (beforeConstructor a 1)) (a 2)) tail) := by
  let b := fieldArgs a
  let c := pushed b
  let d := beforeConstructor a
  have hx1 : b 6 = (0 : M) := by simp [b,fieldArgs,hx,hy]
  have hy1 : b 7 = (0 : M) := by simp [b,fieldArgs,hx,hy]
  have hx2 : c 6 = (0 : M) := by simp [c,pushed,hx1]
  have hx3 : d 6 = (0 : M) := by simp [d,beforeConstructor,hx2,c,b]
  have hy3 : d 7 = (0 : M) := by simp [d,beforeConstructor,pushed,b,fieldArgs,hy]
  have hs : d 2 = cantor (a 1) (a 2) := by simp [d,beforeConstructor,pushed,b,fieldArgs]
  have h1 := PA194M5MPField.field a tail hx hy
  have h2 := PA194M5MPPush.entry b tail hx1 hy1
  have h3 := PA194M5MPCopy.entry c tail hx2
  change ReachesPositive program (sourceState 3647 c tail) (sourceState 3654 d tail) at h3
  have h4 := PA194M5MPConstructor.build d tail (a 1) (a 2) hx3 hy3 hs
  exact appendPositive program (append program (append program h1.reaches h2.reaches) h3.reaches) h4
#print axioms throughConstructor
end models
end PA194M5MPPrefix
