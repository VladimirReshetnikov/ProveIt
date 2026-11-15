import PA194Site38PositiveClockExists
import PA194Site39ClockExists
import PA194SourceSite40Physical
import PA194Site38PositivePath
import PA194SourceSite38Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194SourceSite38DrainStep
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
    let out := PA194Site39OutputFile.updated a count
    out 7 = m ∧ out 6 = args 6+1 ∧
    out 10 = F PA194OneSpareReturn.repeatOutput ![F Code.succ (fun _ => count),(0 : M)] ∧
    ∀ i : Fin 11, i ≠ 7 → i ≠ 6 → i ≠ 10 → out i = args i := by
  classical
  dsimp only [PA194Site39OutputFile.updated]
  refine ⟨?_,?_,?_,?_⟩
  · simp
  · simp
  · simp
  · intro i h7 h6 h10
    simp [Function.update_of_ne h7,Function.update_of_ne h6,Function.update_of_ne h10]
#print axioms updatedRegisters

theorem drainStep (k count tail m : M) (args : Fin 11 → M)
    (hm : args 7 = m+1)
    (he : PA194RegisterPermutation.physicalArgs args 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)]) :
    let a := Function.update args 7 m
    let out := PA194Site39OutputFile.updated a count
    ∃ c38 c39 : M,
      F step ![F step ![F step ![sourceState 38 args tail]]] = sourceState 38 out tail ∧
      F PA194Stepper.stepper ![modelNumeral M 40,
        F PA194Stepper.stepper ![c39,F PA194Stepper.stepper ![c38,physicalFrame 38 ((k+1)+1) args]]] =
        physicalFrame 38 (((k+1)+1)+1) out := by
  dsimp only
  let a := Function.update args 7 m
  let out := PA194Site39OutputFile.updated a count
  have hea : PA194RegisterPermutation.physicalArgs a 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)] := by
    change Function.update args 7 m 10 = _
    rw [Function.update_of_ne (by decide)]
    exact he
  obtain ⟨c38,h38⟩ := PA194Site38PositiveClockExists.existsClock k m args hm
  obtain ⟨c39,h39⟩ := PA194Site39ClockExists.existsClock k count a hea
  have hc38 := (PA194SourceSite38Controller.positiveBranch args tail m hm)
  have hc39 := (PA194SourceSite39Controller.controllerStep a tail (F PA194OneSpareReturn.repeatOutput ![F Code.succ (fun _ => count),(0 : M)]))
  change F step ![sourceState 39 a tail] = sourceState 40 out tail at hc39
  have hc40 := (PA194SourceSite40Physical.sourcePhysical ((k+1)+1) tail out).1
  have hp40 := (PA194SourceSite40Physical.sourcePhysical ((k+1)+1) tail out).2
  refine ⟨c38,c39,?_,?_⟩
  · rw [hc38,hc39,hc40]
  · rw [h38,h39,hp40]
#print axioms drainStep
end models
end PA194SourceSite38DrainStep
