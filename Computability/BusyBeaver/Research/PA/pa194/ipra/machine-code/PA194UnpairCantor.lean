import PA194UnpairDrainComplete
import PA194MachineProjections
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194UnpairCantor
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASubAddition
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SchedulerFetchPositive PA194SourceFetchLoop PA194SourceFetchRestoreLoop PA194UnpairRound PA194UnpairDrainComplete PA194MachineProjections
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

def invariant (p : M) (args : Fin 11 → M) : Prop :=
  cantor (args 6) (args 7) + args 8 = p

theorem positiveCantor (a b w : M) :
    cantor a (b+1) + w = cantor (a+1) b + (w+1) := by
  unfold cantor
  have h : a+(b+1) = (a+1)+b := by ac_rfl
  rw [h]
  ac_rfl

theorem zeroCantor (b w : M) :
    cantor (b+1) (0 : M) + w = cantor 0 b + (w+1) := by
  simp only [cantor,add_zero,zero_add,triangle_succ]
  ac_rfl

theorem positiveRoundInvariant (p : M) (args : Fin 11 → M) (tail w a : M)
    (hw : args 8 = w+1) (ha : args 6 = a+1) (hInv : invariant p args) :
    let a1 := Function.update args 8 w
    let a2 := Function.update a1 7 (a1 7+1)
    let out := Function.update a2 6 a
    F step ![F step ![F step ![F step ![F step ![sourceState 34 args tail]]]]] = sourceState 34 out tail ∧ invariant p out := by
  let a1 := Function.update args 8 w
  let a2 := Function.update a1 7 (a1 7+1)
  let out := Function.update a2 6 a
  have h := positiveRound args tail w a hw ha
  refine ⟨h.1,?_⟩
  have hInv' : cantor (a+1) (args 7) + (w+1) = p := by simpa [invariant,ha,hw] using hInv
  simpa [invariant,out,a2,a1,positiveCantor] using hInv'

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem zeroRoundInvariant (p : M) (args : Fin 11 → M) (tail w : M)
    (hw : args 8 = w+1) (hx : args 6 = (0 : M)) (hInv : invariant p args) :
    let a1 := Function.update args 8 w
    let a2 := Function.update a1 7 (a1 7+1)
    let out := PA194UnpairDrainInvariant.argsAt a2 (a2 7)
    F run ![(((0 : M)+1)+1)+1 + ((PA194UnpairDrainInvariant.three (a2 7)+1)+1),sourceState 34 args tail] = sourceState 34 out tail ∧ invariant p out := by
  let a1 := Function.update args 8 w
  let a2 := Function.update a1 7 (a1 7+1)
  let out := PA194UnpairDrainInvariant.argsAt a2 (a2 7)
  have h := zeroXRound args tail w hw hx
  refine ⟨h.1,?_⟩
  have hInv' : cantor (0 : M) (args 7) + (w+1) = p := by simpa [invariant,hx,hw] using hInv
  change cantor (out 6) (out 7) + out 8 = p
  have h6 : out 6 = args 7+1 := h.2.2.1
  have h7 : out 7 = 0 := h.2.2.2.1
  have h8 : out 8 = w := h.2.1
  rw [h6,h7,h8,zeroCantor]
  exact hInv'

omit [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem exitIdentifies (p : M) (args : Fin 11 → M) (tail : M)
    (hz : args 8 = (0 : M)) (hInv : invariant p args) :
    F step ![sourceState 34 args tail] = sourceState 42 args tail ∧
    F fixedFirst ![p] = args 6 ∧ F fixedSecond ![p] = args 7 := by
  have hp : cantor (args 6) (args 7) = p := by simpa [invariant,hz] using hInv
  refine ⟨sourceDecZero 34 42 8 (some 35) (by decide) inst34 args tail hz,?_,?_⟩
  · rw [←hp,fixedFirst_model,first_cantor]
  · rw [←hp,fixedSecond_model,second_cantor]
#print axioms positiveCantor
#print axioms zeroCantor
#print axioms positiveRoundInvariant
#print axioms zeroRoundInvariant
#print axioms exitIdentifies
end models
end PA194UnpairCantor
