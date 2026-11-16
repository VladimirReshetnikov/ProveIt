import PA194ModelMPFields
import PA194ModelMPCopy
import PA194ModelMPPush
import PA194ModelMPImp
import PA194ModelMPGuard
import PA194ModelMPField

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace PA194ModelMPCommand
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194MPLiteralRows
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
    let h := impValue (a 1) (b 4) = a 5
    Function.update (Function.update (Function.update b 5 0) 1 (if h then b 4 else 0))
      2 (if h then cantor 0 (a 2) else a 2)

/-- Actual model-length MP command from the resolved source entry back to the
scheduler dispatch frame. Both outcomes preserve the unrelated registers. -/
theorem command (a : Fin 11 → M) (tail : M) (hX : a 6 = 0) (hY : a 7 = 0) :
    ReachesPositive (sourceState 3554 a tail) (sourceState 25 (result a) tail) := by
  classical
  let b := fieldArgs a
  let p := PA194ModelMPPush.pushed b
  let d := Function.update p 1 (p 1+p 4)
  let i := PA194ModelMPImp.implicationArgs d (impValue (b 1) (d 1)) (b 2)
  let g := PA194ModelMPGuard.clear i
  have hf := field a tail hX hY
  have hb6 : b 6 = (0 : M) := by simp [b,fieldArgs,hX]
  have hb7 : b 7 = (0 : M) := by simp [b,fieldArgs,hY]
  have hp := PA194ModelMPPush.push 3568 PA194ModelMPPush.entryRows b tail hb6 hb7
  have hp6 : p 6 = (0 : M) := by simp [p,PA194ModelMPPush.pushed,hb6]
  have hcopy := PA194ModelMPCopy.copy 3587 PA194ModelMPCopy.entryRows p tail hp6
  have hd6 : d 6 = (0 : M) := by simp [d,hp6]
  have hd7 : d 7 = (0 : M) := by simp [d,p,PA194ModelMPPush.pushed,hb7]
  have hd2 : d 2 = cantor (b 1) (b 2) := by simp [d,p,PA194ModelMPPush.pushed]
  have hi := PA194ModelMPImp.build d tail (b 1) (b 2) hd6 hd7 hd2
  have hi1 : i 1 = impValue (a 1) (b 4) := by
    simp [i,PA194ModelMPImp.implicationArgs,d,p,PA194ModelMPPush.pushed,b,fieldArgs]
  have hi5 : i 5 = a 5 := by
    simp [i,PA194ModelMPImp.implicationArgs,d,p,PA194ModelMPPush.pushed,b,fieldArgs]
  have hi6 : i 6 = (0 : M) := by simp [i,PA194ModelMPImp.implicationArgs,hd6]
  have hguard := PA194ModelMPGuard.guard i tail hi6
  rw [hi1,hi5] at hguard
  have hpre : Reaches (sourceState 3554 a tail) (sourceState 3621 i tail) :=
    append (append (append hf.reaches hp.reaches) hcopy.reaches) hi.reaches
  by_cases hh : impValue (a 1) (b 4) = a 5
  · rw [if_pos hh] at hguard
    have hg6 : g 6 = (0 : M) := by simp [g,PA194ModelMPGuard.clear,PA194ModelMPCompare.values]
    have hg7 : g 7 = (0 : M) := by
      simp [g,PA194ModelMPGuard.clear,PA194ModelMPCompare.values,i,PA194ModelMPImp.implicationArgs,hd7]
    let s := PA194ModelMPPush.pushed g
    have hs := PA194ModelMPPush.push 3634 PA194ModelMPPush.successRows g tail hg6 hg7
    have hs6 : s 6 = (0 : M) := by simp [s,PA194ModelMPPush.pushed,hg6]
    have hc := PA194ModelMPCopy.copy 3653 PA194ModelMPCopy.successRows s tail hs6
    have he : Function.update s 1 (s 1+s 4) = result a := by
      have hh' : impValue (a 1) (a 4 + F fixedFirst ![a 8]) = a 5 := by
        simpa [b,fieldArgs] using hh
      funext z
      fin_cases z <;> simp [s,g,PA194ModelMPPush.pushed,PA194ModelMPGuard.clear,PA194ModelMPCompare.values,
        i,PA194ModelMPImp.implicationArgs,d,p,PA194ModelMPPush.pushed,b,fieldArgs,result,hh',hX,hY]
    rw [he] at hc
    have hj := PA194SourceFetchLoop.sourceJump 3660 25 (by decide) s3660 (result a) tail
    exact appendPositive (append (append (append hpre hguard.reaches) hs.reaches) hc.reaches)
      (oneStep hj)
  · rw [if_neg hh] at hguard
    have he : g = result a := by
      have hh' : impValue (a 1) (a 4 + F fixedFirst ![a 8]) ≠ a 5 := by
        simpa [b,fieldArgs] using hh
      funext z
      fin_cases z <;> simp [g,PA194ModelMPGuard.clear,PA194ModelMPCompare.values,
        i,PA194ModelMPImp.implicationArgs,d,p,PA194ModelMPPush.pushed,b,fieldArgs,result,hh',hX,hY]
    change ReachesPositive (sourceState 3621 i tail) (sourceState 3660 g tail) at hguard
    rw [he] at hguard
    have hj := PA194SourceFetchLoop.sourceJump 3660 25 (by decide) s3660 (result a) tail
    exact appendPositive (append hpre hguard.reaches) (oneStep hj)

#print axioms command
end models
end PA194ModelMPCommand
