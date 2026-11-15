import PA194DiagonalIteration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194DiagonalLink
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive
open PA194UnpairRound PA194UnpairDrainComplete PA194DiagonalCode PA194DiagonalIteration PA194MachineProjections
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem iterationProjects (start steps : M) :
    let finish := F PA194DiagonalCode.run ![steps,start]
    let p := F scoreCode ![start]+steps
    F fixedFirst ![p] = pi₁ finish ∧ F fixedSecond ![p] = pi₂ finish := by
  let finish := F PA194DiagonalCode.run ![steps,start]
  let p := F scoreCode ![start]+steps
  have hp : cantor (pi₁ finish) (pi₂ finish) = p := (modelScore finish).symm.trans (scoreIteration start steps)
  refine ⟨?_,?_⟩
  · change F fixedFirst ![p] = pi₁ finish
    rw [←hp,fixedFirst_model,first_cantor]
  · change F fixedSecond ![p] = pi₂ finish
    rw [←hp,fixedSecond_model,second_cantor]

theorem positiveRoundMatches (args : Fin 11 → M) (tail w a : M)
    (hw : args 8 = w+1) (ha : args 6 = a+1) :
    let a1 := Function.update args 8 w
    let a2 := Function.update a1 7 (a1 7+1)
    let out := Function.update a2 6 a
    F PA194DiagonalCode.next ![pair (args 6) (args 7)] = pair (out 6) (out 7) := by
  let a1 := Function.update args 8 w
  let a2 := Function.update a1 7 (a1 7+1)
  let out := Function.update a2 6 a
  rw [ha,nextPositive]
  simp [out,a2,a1]

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem zeroRoundMatches (args : Fin 11 → M) (tail w : M)
    (hw : args 8 = w+1) (hx : args 6 = (0 : M)) :
    let a1 := Function.update args 8 w
    let a2 := Function.update a1 7 (a1 7+1)
    let out := PA194UnpairDrainInvariant.argsAt a2 (a2 7)
    F PA194DiagonalCode.next ![pair (args 6) (args 7)] = pair (out 6) (out 7) := by
  let a1 := Function.update args 8 w
  let a2 := Function.update a1 7 (a1 7+1)
  let out := PA194UnpairDrainInvariant.argsAt a2 (a2 7)
  have h := zeroXRound args tail w hw hx
  have h6 : out 6 = args 7+1 := h.2.2.1
  have h7 : out 7 = 0 := h.2.2.2.1
  change F PA194DiagonalCode.next ![pair (args 6) (args 7)] = pair (out 6) (out 7)
  rw [hx,nextZero,h6,h7]
#print axioms iterationProjects
#print axioms positiveRoundMatches
#print axioms zeroRoundMatches
end models
end PA194DiagonalLink
