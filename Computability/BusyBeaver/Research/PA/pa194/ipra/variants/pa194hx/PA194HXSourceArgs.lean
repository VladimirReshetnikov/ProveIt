import PA194CompressedSourceArgs
import PA194HXSourceRoot
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194HXSourceArgs
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194SourceRegisters PA194HXAllocation
open PA194CompressedSourceFrame PA194CompressedBoxFiles PA194CompressedBoxOracle
open PA194OneSpareReturn PA194CompressedIncrementOracle
open PA194CompressedSourceArgs (regs spareTail extend logicalSlot extendUpdate extendTail)

def position (r : Fin 9) : Fin 9 := PA194HXAllocation.hx r

theorem position_index (r : Fin 9) : inputOrder (slot (position r)) = logicalSlot r := by
  fin_cases r <;> rfl

theorem inputOrder_inj : Function.Injective inputOrder := by
  have h : ∀ i j : Fin 11, inputOrder i = inputOrder j → i = j := by decide +kernel
  intro i j hij
  exact h i j hij

theorem suffix : inputOrder 10 = 10 := rfl

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def tapeArgs (s count spare : M) : Fin 11 → M := physicalArgs (args s count spare)

theorem physicalUpdate (a : Fin 11 → M) (r : Fin 9) (v : M) :
    physicalArgs (Function.update a (logicalSlot r) v) =
      Function.update (physicalArgs a) (slot (position r)) v := by
  funext i
  simp only [physicalArgs]
  rw [←position_index r]
  by_cases hi : i = slot (position r)
  · subst i
    simp only [Function.update_self]
  · have h : inputOrder i ≠ inputOrder (slot (position r)) := fun h => hi (inputOrder_inj h)
    simp only [Function.update_of_ne h,Function.update_of_ne hi]
    rfl

theorem physicalTailUpdate (a : Fin 11 → M) (v : M) :
    physicalArgs (Function.update a 10 v) = Function.update (physicalArgs a) 10 v := by
  funext i
  simp only [physicalArgs]
  conv_lhs => rw [←suffix]
  by_cases hi : i = 10
  · subst i
    simp only [Function.update_self]
  · have h : inputOrder i ≠ inputOrder 10 := fun h => hi (inputOrder_inj h)
    simp only [Function.update_of_ne h,Function.update_of_ne hi]
    rfl

theorem readRegister (s count spare : M) (r : Fin 9) :
    tapeArgs s count spare (slot (position r)) = regs s r := by
  unfold tapeArgs physicalArgs
  rw [position_index r]
  simp only [args,logicalSlot,Fin.snoc_castSucc,regs]

theorem readTail (s count spare : M) : tapeArgs s count spare 10 = spareTail count := by
  unfold tapeArgs physicalArgs args spareTail
  rw [suffix]
  change Fin.snoc _ _ (Fin.last 10) = _
  rw [Fin.snoc_last]

theorem frameFile (s count spare : M) :
    F PA194HXAllocation.sourceFileCode (args s count spare) = file (tapeArgs s count spare) :=
  modelSourceFile _

theorem sameRegisters (s s' count spare : M) (hr : regs s' = regs s) :
    tapeArgs s' count spare = tapeArgs s count spare := by
  unfold tapeArgs
  change physicalArgs (extend (regs s') spare (spareTail count)) =
    physicalArgs (extend (regs s) spare (spareTail count))
  rw [hr]

theorem updatedRegisters (s s' count spare v : M) (r : Fin 9)
    (hr : regs s' = Function.update (regs s) r v) :
    tapeArgs s' count spare = Function.update (tapeArgs s count spare) (slot (position r)) v := by
  change physicalArgs (extend (regs s') spare (spareTail count)) = _
  rw [hr,extendUpdate,physicalUpdate]
  rfl

theorem incrementRegisters (s s' count spare : M) (r : Fin 9)
    (hr : regs s' = Function.update (regs s) r (F Code.succ (fun _ => regs s r))) :
    tapeArgs s' (count+1) spare = incremented (tapeArgs s count spare) count (position r) := by
  unfold incremented
  have hslot : slot (position r) ≠ (10 : Fin 11) := by
    intro h
    have hv := congrArg Fin.val h
    change (position r).val = 10 at hv
    have := (position r).isLt
    omega
  rw [←Function.update_comm hslot]
  change physicalArgs (extend (regs s') spare (spareTail (count+1))) =
    Function.update (Function.update (tapeArgs s count spare) (slot (position r))
      (tapeArgs s count spare (slot (position r))+1)) 10 (spareTail (count+1))
  rw [extendTail (regs s') spare (spareTail count),physicalTailUpdate]
  change Function.update (tapeArgs s' count spare) 10 (spareTail (count+1)) = _
  rw [updatedRegisters s s' count spare _ r hr,readRegister,←modelAddOne]
  rfl

#print axioms readRegister
#print axioms frameFile
#print axioms updatedRegisters
#print axioms incrementRegisters
end models
end PA194HXSourceArgs
