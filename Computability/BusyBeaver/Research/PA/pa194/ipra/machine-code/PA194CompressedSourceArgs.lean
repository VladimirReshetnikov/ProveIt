import PA194CompressedSourceFrame
import PA194CompressedIncrementOracle

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194CompressedSourceArgs
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194SourceRegisters PA194RegisterPermutation
open PA194CompressedSourceFrame PA194CompressedBoxFiles PA194CompressedBoxOracle
open PA194OneSpareReturn PA194CompressedIncrementOracle M6.Source

def position (r : Fin 9) : Fin 9 := ⟨physicalRegister r,physicalRegister_lt r⟩
def logicalSlot (r : Fin 9) : Fin 11 := r.castSucc.castSucc

theorem position_index (r : Fin 9) : inputOrder (slot (position r)) = logicalSlot r :=
  inversePhysical r

theorem inputOrder_inj : Function.Injective inputOrder := by
  have h : ∀ i j : Fin 11, inputOrder i = inputOrder j → i = j := by decide +kernel
  intro i j hij
  exact h i j hij

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def regs (s : M) : Fin 9 → M := fun r => getSem r.val (pi₂ s)

noncomputable def spareTail (count : M) : M := F repeatOutput ![count,(0 : M)]

def extend (r : Fin 9 → M) (spare tail : M) : Fin 11 → M :=
  Fin.snoc (Fin.snoc r spare) tail

noncomputable def tapeArgs (s count spare : M) : Fin 11 → M := physicalArgs (args s count spare)

theorem extendUpdate (a : Fin 9 → M) (spare tail v : M) (r : Fin 9) :
    extend (Function.update a r v) spare tail = Function.update (extend a spare tail) (logicalSlot r) v := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hh : Fin.last 10 ≠ logicalSlot r := by
      intro h
      have hv := congrArg Fin.val h
      change 10 = r.val at hv
      have := r.isLt
      omega
    rw [Function.update_of_ne hh]
    simp only [extend,Fin.snoc_last]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · have hh : (Fin.last 9).castSucc ≠ logicalSlot r := by
        intro h
        have hv := congrArg Fin.val h
        change 9 = r.val at hv
        have := r.isLt
        omega
      rw [Function.update_of_ne hh]
      simp only [extend,Fin.snoc_castSucc,Fin.snoc_last]
    · by_cases h : k = r
      · subst k
        have hself := Function.update_self (a := logicalSlot r) (v := v) (f := extend a spare tail)
        change extend (Function.update a r v) spare tail (logicalSlot r) =
          Function.update (extend a spare tail) (logicalSlot r) v (logicalSlot r)
        rw [hself]
        simp only [extend,logicalSlot,Fin.snoc_castSucc,Function.update_self]
      · have hh : k.castSucc.castSucc ≠ logicalSlot r := by
          intro he
          have hv := congrArg (Fin.val : Fin 11 → Nat) he
          exact h (Fin.ext hv)
        rw [Function.update_of_ne hh]
        simp only [extend,Fin.snoc_castSucc,Function.update_of_ne h]

theorem extendTail (a : Fin 9 → M) (spare tail nextTail : M) :
    extend a spare nextTail = Function.update (extend a spare tail) 10 nextTail := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [show Fin.last 10 = (10 : Fin 11) from rfl,Function.update_self]
    exact Fin.snoc_last _ _
  · have hh : j.castSucc ≠ (10 : Fin 11) := by
      intro h
      have hv := congrArg Fin.val h
      change j.val = 10 at hv
      have := j.isLt
      omega
    rw [Function.update_of_ne hh]
    simp only [extend,Fin.snoc_castSucc]

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
    F sourceFileCode (args s count spare) = file (tapeArgs s count spare) :=
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

#print axioms incrementRegisters
#print axioms updatedRegisters
end models
end PA194CompressedSourceArgs
