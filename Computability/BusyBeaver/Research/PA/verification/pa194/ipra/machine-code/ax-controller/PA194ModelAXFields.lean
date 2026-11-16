import PA194SchedulerIteration
import TableDispatch

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194ModelAXFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAHerbrandSelection PRAExhaustion TableDispatch
open PA194SchedulerIteration PA194SchedulerCode PA194MachineShiftMPCode
open PA194MachineAXCode PA194MachineStack

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem selectedArgument (s c : M) (htag : F (head fN fL) ![s] = (c+1)+1) :
    F (axArg fN fL) ![s] = c := by
  rw [axArg,PA194PathIterator.modelUnary,PA194PathIterator.modelUnary,htag]
  have hp (u : M) : F predCode (fun _ => u+1) = u := by
    change F predCode (fun _ => F addCode ![u,F oneCode Fin.elim0]) = u
    rw [modelAddOne,modelPredSucc]
  simp only [hp]

/-- Evaluate the modeled AX command for tag c+2. -/
theorem nextFields (s c : M) (htag : F (head fN fL) ![s] = (c+1)+1) :
    let y := F (yArg fN fL) ![s]
    let x := F (xArg fN fL) ![s]
    let d := F fD ![s]
    let h := F fH ![s]
    let ns := F PA194SchedulerIteration.step ![s]
    F fN ![ns] = F (nextN fN fL) ![s] ∧
    F fL ![ns] = F (tail3 fN fL) ![s] ∧
    F fT ![ns] = axTop (h+y) (d+x) c ∧
    F fW ![ns] = axStack (d+x) (h+y) c d h (F fT ![s]) (F fW ![s]) ∧
    F fD ![ns] = 0 ∧ F fH ![ns] = 0 ∧ F haltAt ![s] = 0 := by
  let ns := F PA194SchedulerIteration.step ![s]
  have harg := selectedArgument s c htag
  have hpos : (0 : M) < c+1 :=
    lt_of_le_of_lt zero_le (lt_add_of_pos_right c (Arithmetic.zero_lt_one : (0 : M) < 1))
  have htall : (1 : M) < (c+1)+1 := by
    have h := add_lt_add_right hpos (1 : M)
    simpa only [add_zero,add_comm (1 : M) (c+1)] using h
  have h0 : F (head fN fL) ![s] ≠ (0 : M) := by
    rw [htag]
    exact ne_of_gt (lt_trans Arithmetic.zero_lt_one htall)
  have h1 : F (head fN fL) ![s] ≠ (1 : M) := by
    rw [htag]
    exact ne_of_gt htall
  have n : F fN ![ns] = F (nextN fN fL) ![s] := by
    simp only [ns,step,pack_model,fN,fst_model,modelProjection,Matrix.cons_val_zero,pi₁_pair]
  have l : F fL ![ns] = F (nextL fN fL) ![s] := by
    simp only [ns,step,pack_model,fL,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  have d : F fD ![ns] = F (nextD fN fL fD) ![s] := by
    simp only [ns,step,pack_model,fD,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  obtain ⟨ht,hw,hh⟩ := step_fields s
  refine ⟨n,?_,?_,?_,?_,?_,?_⟩
  · rw [l,nextL,choose0_model,if_neg h0,choose1_model,if_neg h1]
  · rw [ht,nextTop,choose0_model,if_neg h0,choose1_model,if_neg h1,axTop_model,harg]
  · rw [hw,nextStack,choose0_model,if_neg h0,choose1_model,if_neg h1,axStack_model,harg]
  · rw [d,nextD,choose0_model,if_neg h0,choose1_model,if_neg h1]
    exact PRAMultiplication.modelZero _
  · rw [hh,nextCache,choose0_model,if_neg h0]
    exact PRAMultiplication.modelZero _
  · rw [haltAt,halt,choose0_model,if_neg h0]
    exact PRAMultiplication.modelZero _

#print axioms selectedArgument
#print axioms nextFields
end models
end PA194ModelAXFields
