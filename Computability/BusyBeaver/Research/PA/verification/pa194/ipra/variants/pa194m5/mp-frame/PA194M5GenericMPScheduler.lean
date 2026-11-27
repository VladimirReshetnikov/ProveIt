import PA194M5MPArithmetic
import PA194ModelMPFields
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194M5GenericMPScheduler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SchedulerCode PA194SchedulerIteration PA194MachineShiftMPCode PA194M5MPArithmetic
open PA194TargetCantor PA194MachineProjections PA194ModelMPFields
open PA194SourceControllerCode PA194IteratedSimulation
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

/-- A scheduler with arbitrary AX branches and the AX11H ordinary-MP branches. -/
noncomputable def stepAlt (axL axT axW axD axH : Code 1) : Code 1 :=
  pack (nextN fN fL)
    (choose0 (head fN fL) (PA194SchedulerCode.tail fN fL) (choose1 (head fN fL) (tail2 fN fL) axL))
    (choose0 (head fN fL) fH (choose1 (head fN fL) (mpTop5 fT fH fD (yArg fN fL)) axT))
    (choose0 (head fN fL) (shiftStack fW) (choose1 (head fN fL) (mpStack5 fT fW fH fD (yArg fN fL)) axW))
    (choose0 (head fN fL) fD (choose1 (head fN fL) (mpArg fD (yArg fN fL)) axD))
    (choose0 (head fN fL) (shiftCache fW) (choose1 (head fN fL) (.zero 1) axH))

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

theorem nextFields (s : M) (hMP : F (head fN fL) ![s] = 1) (axL axT axW axD axH : Code 1) :
    let field := F (PA194SchedulerCode.tail fN fL) ![s]
    let d := F fD ![s] + F fixedFirst ![field]
    let ok := PA194ProgramCons.implicationValue 5 (F fT ![s]) d = F fH ![s]
    let ns := F (stepAlt axL axT axW axD axH) ![s]
    F fN ![ns] = F (nextN fN fL) ![s] ∧
    F fL ![ns] = F fixedSecond ![field] ∧
    F fT ![ns] = (if ok then d else 0) ∧
    F fW ![ns] = (if ok then cantor 0 (F fW ![s]) else F fW ![s]) ∧ F fD ![ns] = d ∧ F fH ![ns] = 0 := by
  let field := F (PA194SchedulerCode.tail fN fL) ![s]
  let d := F fD ![s] + F fixedFirst ![field]
  let ok := PA194ProgramCons.implicationValue 5 (F fT ![s]) d = F fH ![s]
  let ns := F (stepAlt axL axT axW axD axH) ![s]
  have h0 : F (head fN fL) ![s] ≠ (0:M) := by rw [hMP]; exact ne_of_gt (_root_.zero_lt_one)
  have hn : F fN ![ns] = F (nextN fN fL) ![s] := by
    simp only [ns,stepAlt,pack_model,fN,fst_model,modelProjection,Matrix.cons_val_zero,pi₁_pair]
  have hl : F fL ![ns] = F (choose0 (head fN fL) (PA194SchedulerCode.tail fN fL) (choose1 (head fN fL) (tail2 fN fL) axL)) ![s] := by
    simp only [ns,stepAlt,pack_model,fL,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  have ht : F fT ![ns] = F (choose0 (head fN fL) fH (choose1 (head fN fL) (mpTop5 fT fH fD (yArg fN fL)) axT)) ![s] := by
    simp only [ns,stepAlt,pack_model,fT,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  have hw : F fW ![ns] = F (choose0 (head fN fL) (shiftStack fW) (choose1 (head fN fL) (mpStack5 fT fW fH fD (yArg fN fL)) axW)) ![s] := by
    simp only [ns,stepAlt,pack_model,fW,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  have hd : F fD ![ns] = F (choose0 (head fN fL) fD (choose1 (head fN fL) (mpArg fD (yArg fN fL)) axD)) ![s] := by
    simp only [ns,stepAlt,pack_model,fD,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  have hh : F fH ![ns] = F (choose0 (head fN fL) (shiftCache fW) (choose1 (head fN fL) (.zero 1) axH)) ![s] := by
    simp only [ns,stepAlt,pack_model,fH,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  refine ⟨hn,?_,?_,?_,?_,?_⟩
  · rw [hl,choose0_model,if_neg h0,choose1_model,if_pos hMP,suffix]
  · rw [ht,choose0_model,if_neg h0,choose1_model,if_pos hMP,mpTop5_model,operand]
  · rw [hw,choose0_model,if_neg h0,choose1_model,if_pos hMP,mpStack5_model,operand]
  · rw [hd,choose0_model,if_neg h0,choose1_model,if_pos hMP,mpArg,modelBin,operand]
    rfl
  · rw [hh,choose0_model,if_neg h0,choose1_model,if_pos hMP]
    exact PRAMultiplication.modelZero _
#print axioms nextFields
end models
end PA194M5GenericMPScheduler
