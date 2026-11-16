import PA194ProgramReader
import PA194M5Program
import PA194ModelMPField
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194M5MPField
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194ProgramDrain PA194ProgramReader PA194M5Program
open PA194MachineProjections PA194ModelMPField
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

theorem fieldRows : ReaderRows program 3614 8 4 := by
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,by decide,by decide,by decide,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | rw [programLength]; decide | decide +kernel
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

theorem field (a : Fin 11 → M) (tail : M) (hX : a 6 = 0) (hY : a 7 = 0) :
    ReachesPositive program (sourceState 3614 a tail) (sourceState 3628 (fieldArgs a) tail) := by
  have h := PA194ProgramReader.reader program 3614 8 4 fieldRows a tail
  dsimp only at h
  have hz : cantor (0 : M) 0 = 0 := by simp [cantor,triangle]
  rw [hX,hY,hz,zero_add] at h
  let x := F fixedFirst ![a 8]
  let y := F fixedSecond ![a 8]
  have ho := PA194AXReaderAlgebra.outputD a x y
  dsimp only at ho
  change ReachesPositive program _ (sourceState 3628
    (PA194ModelMPDrain.argsAfter (PA194ModelMPDrain.argsAfter (PA194AXReaderAlgebra.decoded a x y) 7 [8]
      (PA194AXReaderAlgebra.decoded a x y 7)) 6 [4]
      ((PA194ModelMPDrain.argsAfter (PA194AXReaderAlgebra.decoded a x y) 7 [8]
      (PA194AXReaderAlgebra.decoded a x y 7)) 6)) tail) at h
  rw [ho] at h
  have hs : Function.update (Function.update (fieldArgs a) 6 0) 7 0 = fieldArgs a := by
    funext i
    fin_cases i <;> simp [fieldArgs,hX,hY]
  exact hs ▸ h
#print axioms fieldRows
#print axioms field
end models
end PA194M5MPField
