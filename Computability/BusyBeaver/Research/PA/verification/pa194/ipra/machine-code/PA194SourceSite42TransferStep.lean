import PA194Site42PositiveClockExists
import PA194Site43ClockExists
import PA194SourceSite44Physical
import PA194Site42PositivePath
import PA194SourceSite42Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194SourceSite42TransferStep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SourceControllerCode PA194SourceSite31Controller PA194SourceSite31Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem updatedRegisters (args : Fin 11 → M) (m count : M) :
    let a := Function.update args 7 m
    let out := PA194Site43OutputFile.updated a count
    out 7 = m ∧ out 8 = args 8+1 ∧
    out 10 = F PA194OneSpareReturn.repeatOutput ![F Code.succ (fun _ => count),(0 : M)] ∧
    ∀ i : Fin 11, i ≠ 7 → i ≠ 8 → i ≠ 10 → out i = args i := by
  classical
  dsimp only [PA194Site43OutputFile.updated]
  refine ⟨?_,?_,?_,?_⟩
  · simp
  · simp
  · simp
  · intro i h7 h8 h10
    simp [Function.update_of_ne h7,Function.update_of_ne h8,Function.update_of_ne h10]
#print axioms updatedRegisters

theorem transferStep (k count tail m : M) (args : Fin 11 → M)
    (hm : args 7 = m+1)
    (he : PA194RegisterPermutation.physicalArgs args 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)]) :
    let a := Function.update args 7 m
    let out := PA194Site43OutputFile.updated a count
    ∃ c42 c43 : M,
      F step ![F step ![F step ![sourceState 42 args tail]]] = sourceState 42 out tail ∧
      F PA194Stepper.stepper ![modelNumeral M 36,
        F PA194Stepper.stepper ![c43,F PA194Stepper.stepper ![c42,physicalFrame 42 ((k+1)+1) args]]] =
        physicalFrame 42 (((k+1)+1)+1) out := by
  dsimp only
  let a := Function.update args 7 m
  let out := PA194Site43OutputFile.updated a count
  have hea : PA194RegisterPermutation.physicalArgs a 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)] := by
    change Function.update args 7 m 10 = _
    rw [Function.update_of_ne (by decide)]
    exact he
  obtain ⟨c42,h42⟩ := PA194Site42PositiveClockExists.existsClock k m args hm
  obtain ⟨c43,h43⟩ := PA194Site43ClockExists.existsClock k count a hea
  have hc42 := (PA194SourceSite42Controller.positiveBranch args tail m hm)
  have hc43 := (PA194SourceSite43Controller.controllerStep a tail (F PA194OneSpareReturn.repeatOutput ![F Code.succ (fun _ => count),(0 : M)]))
  change F step ![sourceState 43 a tail] = sourceState 44 out tail at hc43
  have hc44 := (PA194SourceSite44Physical.sourcePhysical ((k+1)+1) tail out).1
  have hp44 := (PA194SourceSite44Physical.sourcePhysical ((k+1)+1) tail out).2
  refine ⟨c42,c43,?_,?_⟩
  · rw [hc42,hc43,hc44]
  · rw [h42,h43,hp44]
#print axioms transferStep
end models
end PA194SourceSite42TransferStep
