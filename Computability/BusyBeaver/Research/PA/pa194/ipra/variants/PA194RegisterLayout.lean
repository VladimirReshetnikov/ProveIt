import PA194CompressedSourceArgs
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194RegisterLayout
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open PRAModelIOpenPairing PA194SourceRegisters
open PA194CompressedSourceFrame PA194CompressedBoxFiles PA194CompressedBoxOracle
open PA194OneSpareReturn PA194CompressedIncrementOracle
open PA194CompressedSourceArgs (regs spareTail extend logicalSlot extendUpdate extendTail)

/-- A physical allocation of the nine logical registers and the unchanged
    suffix of the repeated-spare file. -/
structure Allocation where
  order : Fin 11 → Fin 11
  position : Fin 9 → Fin 9
  position_index : ∀ r, order (slot (position r)) = logicalSlot r
  order_inj : Function.Injective order
  first_spare : order 9 = 9
  suffix : order 10 = 10

def physicalArgs (A : Allocation) {M : Type} (e : Fin 11 → M) : Fin 11 → M :=
  e ∘ A.order

def sourceFileCode (A : Allocation) : Code 11 :=
  .comp (PA194RegisterFile.fileCode 10) (pack 11 (fun i => .proj (A.order i)))

section models
variable (A : Allocation)
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def tapeArgs (s count spare : M) : Fin 11 → M := physicalArgs A (args s count spare)

theorem physicalUpdate (a : Fin 11 → M) (r : Fin 9) (v : M) :
    physicalArgs A (Function.update a (logicalSlot r) v) =
      Function.update (physicalArgs A a) (slot (A.position r)) v := by
  funext i
  simp only [physicalArgs, Function.comp_apply]
  rw [←A.position_index r]
  by_cases hi : i = slot (A.position r)
  · subst i
    simp only [Function.update_self]
  · have h : A.order i ≠ A.order (slot (A.position r)) := fun h => hi (A.order_inj h)
    simp only [Function.update_of_ne h,Function.update_of_ne hi]
    rfl

theorem physicalTailUpdate (a : Fin 11 → M) (v : M) :
    physicalArgs A (Function.update a 10 v) = Function.update (physicalArgs A a) 10 v := by
  funext i
  simp only [physicalArgs, Function.comp_apply]
  conv_lhs => rw [←A.suffix]
  by_cases hi : i = 10
  · subst i
    simp only [Function.update_self]
  · have h : A.order i ≠ A.order 10 := fun h => hi (A.order_inj h)
    simp only [Function.update_of_ne h,Function.update_of_ne hi]
    rfl

theorem readRegister (s count spare : M) (r : Fin 9) :
    tapeArgs A s count spare (slot (A.position r)) = regs s r := by
  simp only [tapeArgs, physicalArgs, Function.comp_apply]
  rw [A.position_index r]
  simp only [args,logicalSlot,Fin.snoc_castSucc,regs]

theorem readTail (s count spare : M) : tapeArgs A s count spare 10 = spareTail count := by
  simp only [tapeArgs, physicalArgs, Function.comp_apply, args, spareTail]
  rw [A.suffix]
  change Fin.snoc _ _ (Fin.last 10) = _
  rw [Fin.snoc_last]

theorem frameFile (s count spare : M) :
    F (sourceFileCode A) (args s count spare) = file (tapeArgs A s count spare) := by
  rw [sourceFileCode, modelComposition, getCode_pack]
  congr 1
  funext i
  exact modelProjection (A.order i) _

theorem sameRegisters (s s' count spare : M) (hr : regs s' = regs s) :
    tapeArgs A s' count spare = tapeArgs A s count spare := by
  unfold tapeArgs
  change physicalArgs A (extend (regs s') spare (spareTail count)) =
    physicalArgs A (extend (regs s) spare (spareTail count))
  rw [hr]

theorem updatedRegisters (s s' count spare v : M) (r : Fin 9)
    (hr : regs s' = Function.update (regs s) r v) :
    tapeArgs A s' count spare = Function.update (tapeArgs A s count spare) (slot (A.position r)) v := by
  change physicalArgs A (extend (regs s') spare (spareTail count)) = _
  rw [hr,extendUpdate,physicalUpdate A]
  rfl

theorem incrementRegisters (s s' count spare : M) (r : Fin 9)
    (hr : regs s' = Function.update (regs s) r (F Code.succ (fun _ => regs s r))) :
    tapeArgs A s' (count+1) spare = incremented (tapeArgs A s count spare) count (A.position r) := by
  unfold incremented
  have hslot : slot (A.position r) ≠ (10 : Fin 11) := by
    intro h
    have hv := congrArg Fin.val h
    change (A.position r).val = 10 at hv
    have := (A.position r).isLt
    omega
  rw [←Function.update_comm hslot]
  change physicalArgs A (extend (regs s') spare (spareTail (count+1))) =
    Function.update (Function.update (tapeArgs A s count spare) (slot (A.position r))
      (tapeArgs A s count spare (slot (A.position r))+1)) 10 (spareTail (count+1))
  rw [extendTail (regs s') spare (spareTail count),physicalTailUpdate A]
  change Function.update (tapeArgs A s' count spare) 10 (spareTail (count+1)) = _
  rw [updatedRegisters A s s' count spare _ r hr,readRegister,←modelAddOne]
  rfl

#print axioms readRegister
#print axioms frameFile
#print axioms updatedRegisters
#print axioms incrementRegisters
end models
end PA194RegisterLayout
