import PA194SourceSentinel
import PA194ClockInvariantDefinable
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SourceReachable
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PA194FiniteControls PA194StateOne
open PA194SourceControllerCode PA194SourcePCBound PA194SourceSentinel
open PA194ClockInvariantDefinable PA194IteratedSimulation
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem stepPCBound (s : M) (hs : F pc ![s] < modelNumeral M 3675) :
    F pc ![F step ![s]] < modelNumeral M 3675 := by
  obtain ⟨i,hi⟩ := modelBelowNumeral 3675 (F pc ![s]) hs
  by_cases hwork : i.val < 3673
  · apply stepWorkingPCBound
    rw [hi]
    exact modelNumeralStrict i.val 3673 hwork
  · have cases : i.val = 3673 ∨ i.val = 3674 := by have := i.isLt; omega
    rcases cases with hm | hh
    · have hs' : F pc ![s] = modelNumeral M 3673 := by simpa [hm] using hi
      rw [stepMalformed s hs']
      exact hs
    · have hs' : F pc ![s] = modelNumeral M 3674 := by simpa [hh] using hi
      rw [stepHalted s hs']
      exact hs

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- Starting with a bounded encoded PC, the actual finite source-controller
    iteration retains the bound at every model time, including nonstandard. -/
theorem runPCBound (seed : M) (hseed : F pc ![seed] < modelNumeral M 3675) :
    ∀ n : M, F pc ![F run ![n,seed]] < modelNumeral M 3675 := by
  have hr : 𝚺₁-Function₁ (fun n : M => F run ![n,seed]) :=
    bindBinary _ seed (binaryCodeDef (M := M) run)
  have hq : 𝚺₁-Function₁ (fun n : M => F pc ![F run ![n,seed]]) :=
    composeUnary _ _ (unaryCodeDef (M := M) pc) hr
  haveI := hq
  have hp : 𝚺₁-Predicate (fun n : M => F pc ![F run ![n,seed]] < modelNumeral M 3675) := by
    definability
  intro n
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact hp
  | zero => rw [run,iterateZero]; exact hseed
  | succ n ih => rw [run,iterateSucc]; exact stepPCBound _ ih
#print axioms stepPCBound
#print axioms runPCBound
end models
end PA194SourceReachable
