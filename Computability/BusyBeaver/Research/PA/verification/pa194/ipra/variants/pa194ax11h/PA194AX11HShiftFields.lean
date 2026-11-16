import PA194AX11HGenericMPScheduler
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194AX11HShiftFields
open PA194AX11HGenericMPScheduler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SchedulerCode PA194SchedulerIteration PA194MachineShiftMPCode
open PA194TargetCantor PA194MachineProjections PA194ModelMPFields
open PA194SourceControllerCode PA194SchedulerSourceFrame PA194IteratedSimulation

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

theorem nextFields (s : M) (opcode : F (head fN fL) ![s] = 0)
    (axL axT axW axD axH : Code 1) :
    let ns := F (stepAlt axL axT axW axD axH) ![s]
    F fN ![ns] = F (nextN fN fL) ![s] ∧
    F fL ![ns] = F (PA194SchedulerCode.tail fN fL) ![s] ∧
    F fT ![ns] = F fH ![s] ∧
    F fW ![ns] = F fixedSecond ![F fW ![s]] ∧
    F fD ![ns] = F fD ![s] ∧ F fH ![ns] = F fixedFirst ![F fW ![s]] := by
  let ns := F (stepAlt axL axT axW axD axH) ![s]
  have hn : F fN ![ns] = F (nextN fN fL) ![s] := by
    simp only [ns,stepAlt,pack_model,fN,fst_model,modelProjection,Matrix.cons_val_zero,pi₁_pair]
  have hl : F fL ![ns] = F (choose0 (head fN fL) (PA194SchedulerCode.tail fN fL) (choose1 (head fN fL) (tail2 fN fL) axL)) ![s] := by
    simp only [ns,stepAlt,pack_model,fL,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  have ht : F fT ![ns] = F (choose0 (head fN fL) fH (choose1 (head fN fL) (mpTop fT fH fD (yArg fN fL)) axT)) ![s] := by
    simp only [ns,stepAlt,pack_model,fT,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  have hw : F fW ![ns] = F (choose0 (head fN fL) (shiftStack fW) (choose1 (head fN fL) fW axW)) ![s] := by
    simp only [ns,stepAlt,pack_model,fW,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  have hd : F fD ![ns] = F (choose0 (head fN fL) fD (choose1 (head fN fL) (mpArg fD (yArg fN fL)) axD)) ![s] := by
    simp only [ns,stepAlt,pack_model,fD,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  have hh : F fH ![ns] = F (choose0 (head fN fL) (shiftCache fW) (choose1 (head fN fL) (.zero 1) axH)) ![s] := by
    simp only [ns,stepAlt,pack_model,fH,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  have single (v : M) : (fun _ : Fin 1 => v) = ![v] := by
    funext i
    fin_cases i
    rfl
  refine ⟨hn,?_,?_,?_,?_,?_⟩
  · rw [hl,choose0_model,if_pos opcode]
  · rw [ht,choose0_model,if_pos opcode]
  · rw [hw,choose0_model,if_pos opcode,shiftStack,PA194PathIterator.modelUnary,single]
  · rw [hd,choose0_model,if_pos opcode]
  · rw [hh,choose0_model,if_pos opcode,shiftCache,PA194PathIterator.modelUnary,single]

#print axioms nextFields
end models
end PA194AX11HShiftFields
