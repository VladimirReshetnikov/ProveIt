import PA194ModelAXReader
import PA194AXReaderAlgebra
import PA194MPLiteralRows3554

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace PA194ModelMPField
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194MPLiteralRows
open PA194MachineProjections PA194TargetCantor

theorem fieldRows : PA194ModelAXReader.ReaderRows 3554 8 4 :=
  ⟨⟨by decide,s3554,s3555,s3556,s3557,s3558,s3559,s3560,s3561⟩,
    by decide,by decide,by decide,s3562,s3563,s3564,s3565,s3566,s3567,by decide⟩

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

noncomputable def fieldArgs (a : Fin 11 → M) : Fin 11 → M :=
  Function.update (Function.update a 8 (F fixedSecond ![a 8])) 4
    (a 4+F fixedFirst ![a 8])

theorem field (a : Fin 11 → M) (tail : M) (hX : a 6 = 0) (hY : a 7 = 0) :
    ReachesPositive (sourceState 3554 a tail) (sourceState 3568 (fieldArgs a) tail) := by
  have h := PA194ModelAXReader.reader 3554 8 4 fieldRows a tail
  dsimp only at h
  have hz : cantor (0 : M) 0 = 0 := by simp [cantor,triangle]
  rw [hX,hY,hz,zero_add] at h
  let x := F fixedFirst ![a 8]
  let y := F fixedSecond ![a 8]
  have ho := PA194AXReaderAlgebra.outputD a x y
  dsimp only at ho
  change ReachesPositive _ (sourceState 3568
    (argsAfter (argsAfter (PA194AXReaderAlgebra.decoded a x y) 7 [8]
      (PA194AXReaderAlgebra.decoded a x y 7)) 6 [4]
      ((argsAfter (PA194AXReaderAlgebra.decoded a x y) 7 [8]
      (PA194AXReaderAlgebra.decoded a x y 7)) 6)) tail) at h
  rw [ho] at h
  have hs : Function.update (Function.update (fieldArgs a) 6 0) 7 0 = fieldArgs a := by
    funext i
    fin_cases i <;> simp [fieldArgs,hX,hY]
  exact hs ▸ h


#print axioms field
end models
end PA194ModelMPField
