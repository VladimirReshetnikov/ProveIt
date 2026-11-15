import PA194Site45PositiveClockExists
import PA194Site46ClockExists
import PA194SourceSite47Physical
import PA194Site45PositivePath
import PA194SourceSite45Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194SourceSite45TransferStep
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
    let a := Function.update args 6 m
    let out := PA194Site46OutputFile.updated a count
    out 6 = m ∧ out 3 = args 3+1 ∧
    out 10 = F PA194OneSpareReturn.repeatOutput ![F Code.succ (fun _ => count),(0 : M)] ∧
    ∀ i : Fin 11, i ≠ 6 → i ≠ 3 → i ≠ 10 → out i = args i := by
  classical
  dsimp only [PA194Site46OutputFile.updated]
  refine ⟨?_,?_,?_,?_⟩
  · simp
  · simp
  · simp
  · intro i h6 h3 h10
    simp [Function.update_of_ne h6,Function.update_of_ne h3,Function.update_of_ne h10]
#print axioms updatedRegisters

theorem transferStep (k count tail m : M) (args : Fin 11 → M)
    (hm : args 6 = m+1)
    (he : PA194RegisterPermutation.physicalArgs args 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)]) :
    let a := Function.update args 6 m
    let out := PA194Site46OutputFile.updated a count
    ∃ c45 c46 : M,
      F step ![F step ![F step ![sourceState 45 args tail]]] = sourceState 45 out tail ∧
      F PA194Stepper.stepper ![modelNumeral M 30,
        F PA194Stepper.stepper ![c46,F PA194Stepper.stepper ![c45,physicalFrame 45 ((k+1)+1) args]]] =
        physicalFrame 45 (((k+1)+1)+1) out := by
  dsimp only
  let a := Function.update args 6 m
  let out := PA194Site46OutputFile.updated a count
  have hea : PA194RegisterPermutation.physicalArgs a 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)] := by
    change Function.update args 6 m 10 = _
    rw [Function.update_of_ne (by decide)]
    exact he
  obtain ⟨c45,h45⟩ := PA194Site45PositiveClockExists.existsClock k m args hm
  obtain ⟨c46,h46⟩ := PA194Site46ClockExists.existsClock k count a hea
  have hc45 := (PA194SourceSite45Controller.positiveBranch args tail m hm)
  have hc46 := (PA194SourceSite46Controller.controllerStep a tail (F PA194OneSpareReturn.repeatOutput ![F Code.succ (fun _ => count),(0 : M)]))
  change F step ![sourceState 46 a tail] = sourceState 47 out tail at hc46
  have hc47 := (PA194SourceSite47Physical.sourcePhysical ((k+1)+1) tail out).1
  have hp47 := (PA194SourceSite47Physical.sourcePhysical ((k+1)+1) tail out).2
  refine ⟨c45,c46,?_,?_⟩
  · rw [hc45,hc46,hc47]
  · rw [h45,h46,hp47]
#print axioms transferStep
end models
end PA194SourceSite45TransferStep
