import PA194M5MPPrefix
import PA194M5MPGuard
import PA194TargetCantor

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace PA194M5MPCommand
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SchedulerFetchPositive PA194ProgramDrain PA194M5Program
open PA194MachineProjections PA194TargetCantor PA194ModelMPField

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

noncomputable def result (a : Fin 11 → M) : Fin 11 → M := by
  classical
  exact
    let b := fieldArgs a
    let h := PA194ProgramCons.implicationValue 5 (a 1) (b 4) = a 5
    Function.update (Function.update (Function.update b 5 0) 1 (if h then b 4 else 0))
      2 (if h then cantor 0 (a 2) else a 2)

/-- Actual model-length MP command from the resolved source entry back to the
scheduler dispatch frame. Both outcomes preserve the unrelated registers. -/
theorem command (a : Fin 11 → M) (tail : M) (hX : a 6 = 0) (hY : a 7 = 0) :
    ReachesPositive program (sourceState 3614 a tail) (sourceState 25 (result a) tail) := by
  classical
  let b := fieldArgs a
  let d := PA194M5MPPrefix.beforeConstructor a
  let i := PA194ModelMPImp.implicationArgs d (PA194ProgramCons.implicationValue 5 (a 1) (d 1)) (a 2)
  let g := PA194ProgramGuard.clear i
  have hd6 : d 6 = (0 : M) := by
    simp [d, PA194M5MPPrefix.beforeConstructor, PA194ModelMPPush.pushed, fieldArgs, hX]
  have hd7 : d 7 = (0 : M) := by
    simp [d, PA194M5MPPrefix.beforeConstructor, PA194ModelMPPush.pushed, fieldArgs, hY]
  have hi1 : i 1 = PA194ProgramCons.implicationValue 5 (a 1) (b 4) := by
    simp [i,PA194ModelMPImp.implicationArgs,d,PA194M5MPPrefix.beforeConstructor,PA194ModelMPPush.pushed,b,fieldArgs]
  have hi5 : i 5 = a 5 := by
    simp [i,PA194ModelMPImp.implicationArgs,d,PA194M5MPPrefix.beforeConstructor,PA194ModelMPPush.pushed,b,fieldArgs]
  have hi6 : i 6 = (0 : M) := by simp [i,PA194ModelMPImp.implicationArgs,hd6]
  have hguard := PA194M5MPGuard.guard i tail hi6
  rw [hi1,hi5] at hguard
  have hpre : Reaches program (sourceState 3614 a tail) (sourceState 3682 i tail) :=
    (PA194M5MPPrefix.throughConstructor a tail hX hY).reaches
  by_cases hh : PA194ProgramCons.implicationValue 5 (a 1) (b 4) = a 5
  · rw [if_pos hh] at hguard
    have hg6 : g 6 = (0 : M) := by simp [g,PA194ProgramGuard.clear,PA194ProgramCompare.values]
    have hg7 : g 7 = (0 : M) := by
      simp [g,PA194ProgramGuard.clear,PA194ProgramCompare.values,i,PA194ModelMPImp.implicationArgs,hd7]
    let s := PA194ModelMPPush.pushed g
    have hs := PA194M5MPPush.success g tail hg6 hg7
    have hs6 : s 6 = (0 : M) := by simp [s,PA194ModelMPPush.pushed,hg6]
    have hc := PA194M5MPCopy.success s tail hs6
    have he : Function.update s 1 (s 1+s 4) = result a := by
      have hh' : PA194ProgramCons.implicationValue 5 (a 1) (a 4 + F fixedFirst ![a 8]) = a 5 := by
        simpa [b,fieldArgs] using hh
      funext z
      fin_cases z <;> simp [s,g,PA194ModelMPPush.pushed,PA194ProgramGuard.clear,PA194ProgramCompare.values,
        i,PA194ModelMPImp.implicationArgs,d,PA194M5MPPrefix.beforeConstructor,PA194ModelMPPush.pushed,b,fieldArgs,result,hh',hX,hY]
    rw [he] at hc
    have hj := PA194ProgramDrain.sourceJump program 3721 25 (by rw [programLength]; decide) (by decide +kernel) (result a) tail
    exact appendPositive program (append program (append program (append program hpre hguard.reaches) hs.reaches) hc.reaches)
      (oneStep program hj)
  · rw [if_neg hh] at hguard
    have he : g = result a := by
      have hh' : PA194ProgramCons.implicationValue 5 (a 1) (a 4 + F fixedFirst ![a 8]) ≠ a 5 := by
        simpa [b,fieldArgs] using hh
      funext z
      fin_cases z <;> simp [g,PA194ProgramGuard.clear,PA194ProgramCompare.values,
        i,PA194ModelMPImp.implicationArgs,d,PA194M5MPPrefix.beforeConstructor,PA194ModelMPPush.pushed,b,fieldArgs,result,hh',hX,hY]
    change ReachesPositive program (sourceState 3682 i tail) (sourceState 3721 g tail) at hguard
    rw [he] at hguard
    have hj := PA194ProgramDrain.sourceJump program 3721 25 (by rw [programLength]; decide) (by decide +kernel) (result a) tail
    exact appendPositive program (append program hpre hguard.reaches) (oneStep program hj)

#print axioms command
end models
end PA194M5MPCommand
