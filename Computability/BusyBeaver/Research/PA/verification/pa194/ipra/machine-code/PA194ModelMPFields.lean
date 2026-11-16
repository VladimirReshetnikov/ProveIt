import PA194SchedulerIteration

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace PA194ModelMPFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion
open PA194SchedulerCode PA194SchedulerIteration PA194MachineShiftMPCode
open PA194TargetCantor PA194MachineProjections
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

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

theorem operand (s : M) :
    F (yArg fN fL) ![s] = F fixedFirst ![F (tail fN fL) ![s]] := by
  rw [yArg,PA194PathIterator.modelUnary]
  apply congrArg (F fixedFirst)
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem suffix (s : M) :
    F (tail2 fN fL) ![s] = F fixedSecond ![F (tail fN fL) ![s]] := by
  rw [tail2,PA194PathIterator.modelUnary]
  apply congrArg (F fixedSecond)
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

/-- Exact modeled MP store transition, starting with the fetched operand field. -/
theorem nextFields (s : M) (hMP : F (head fN fL) ![s] = 1) :
    let field := F (tail fN fL) ![s]
    let m := F fD ![s]+F fixedFirst ![field]
    let matchOK := impValue (F fT ![s]) m = F fH ![s]
    let ns := F step ![s]
    F fN ![ns] = F (nextN fN fL) ![s] ∧
    F fL ![ns] = F fixedSecond ![field] ∧
    F fT ![ns] = (if matchOK then m else 0) ∧
    F fW ![ns] = (if matchOK then cantor 0 (F fW ![s]) else F fW ![s]) ∧
    F fD ![ns] = m ∧ F fH ![ns] = 0 ∧ F haltAt ![s] = 0 := by
  let field := F (tail fN fL) ![s]
  let m := F fD ![s]+F fixedFirst ![field]
  let matchOK := impValue (F fT ![s]) m = F fH ![s]
  let ns := F step ![s]
  have h0 : F (head fN fL) ![s] ≠ (0 : M) := by rw [hMP]; exact ne_of_gt (_root_.zero_lt_one)
  have n : F fN ![ns] = F (nextN fN fL) ![s] := by
    simp only [ns,step,pack_model,fN,fst_model,modelProjection,Matrix.cons_val_zero,pi₁_pair]
  have l : F fL ![ns] = F (nextL fN fL) ![s] := by
    simp only [ns,step,pack_model,fL,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  have d : F fD ![ns] = F (nextD fN fL fD) ![s] := by
    simp only [ns,step,pack_model,fD,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  obtain ⟨ht,hw,hh⟩ := step_fields s
  have ht' : F (nextTop fN fL fT fW fD fH) ![s] = if matchOK then m else 0 := by
    rw [nextTop,choose0_model,if_neg h0,choose1_model,if_pos hMP,mpTop_model,operand]
  have hw' : F (nextStack fN fL fT fW fD fH) ![s] =
      if matchOK then cantor 0 (F fW ![s]) else F fW ![s] := by
    rw [nextStack,choose0_model,if_neg h0,choose1_model,if_pos hMP,mpStack_model,operand]
  refine ⟨n,?_,ht.trans ht',hw.trans hw',?_,?_,?_⟩
  · rw [l,nextL,choose0_model,if_neg h0,choose1_model,if_pos hMP,suffix]
  · rw [d,nextD,choose0_model,if_neg h0,choose1_model,if_pos hMP,mpArg,modelBin,operand]
    rfl
  · rw [hh,nextCache,choose0_model,if_neg h0]
    exact PRAMultiplication.modelZero _
  · rw [haltAt,halt,choose0_model,if_neg h0]
    exact PRAMultiplication.modelZero _

#print axioms nextFields
end models
end PA194ModelMPFields
