import PA194ClockInvariantDefinable
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ClockedSimulation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PA194CumulativeClock PA194Stepper
open PA194ClockInvariantDefinable PA194ConditionalModelLength
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem simulateCodeRun (run : Code 2) (next cost frame : Code 1) (seed start : M)
    (good : M → Prop) (hgood : 𝚺₁-Predicate good)
    (hinit : good (F run ![0,seed]))
    (hframe : start = F frame ![F run ![0,seed]])
    (hnext : ∀ n : M, F run ![n+1,seed] = F next ![F run ![n,seed]])
    (hpres : ∀ s : M, good s → good (F next ![s]))
    (hsegment : ∀ s : M, good s →
      F stepper ![F cost ![s],F frame ![s]] = F frame ![F next ![s]]) :
    ∀ n : M, good (F run ![n,seed]) ∧
      F stepper ![F (clock run cost) ![n,seed],start] = F frame ![F run ![n,seed]] := by
  have hbase : good (F run ![0,seed]) ∧
      F stepper ![F (clock run cost) ![0,seed],start] = F frame ![F run ![0,seed]] := by
    constructor
    · exact hinit
    · rw [clockZero]
      change F stepper ![F (Code.zero 0) Fin.elim0,start] = _
      rw [modelStepperZero]
      exact hframe
  apply simulateModelLength (fun n => F run ![n,seed]) (fun s => F next ![s])
    (fun s => F frame ![s]) (fun n => F (clock run cost) ![n,seed])
    (fun s => F cost ![s]) good start
  · exact invariantDef run cost frame seed start good hgood
  · exact hbase
  · exact hnext
  · intro n
    have h := clockSucc (M := M) run cost n seed
    have hv : (fun _ : Fin 1 => F run ![n,seed]) = ![F run ![n,seed]] := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [hv] at h
    exact h
  · exact hpres
  · exact hsegment
#print axioms simulateCodeRun
end models
end PA194ClockedSimulation
