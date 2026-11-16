import PA194ControllerSchedulerCore
import PA194ModelAXFields
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194AX11HAXSchedulerFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SchedulerCode PA194SchedulerIteration PA194MachineShiftMPCode PA194ControllerScheduler
open PA194TargetCantor PA194MachineProjections PA194ModelAXFields PA194MachineAXCode PA194MachineStack
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
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

theorem nextFields (s c : M) (htag : F (head fN fL) ![s] = (c+1)+1) :
    let y := F (yArg fN fL) ![s]
    let x := F (xArg fN fL) ![s]
    let d := F fD ![s]
    let h := F fH ![s]
    let ns := F (stepK .top true) ![s]
    F fN ![ns] = F (nextN fN fL) ![s] ∧
    F fL ![ns] = F (tail4 fN fL) ![s] ∧
    F fT ![ns] = 0 ∧
    F fW ![ns] = cantor (axTop (h+y) (d+x) c)
      (axStack (d+x) (h+y) c d h (F fT ![s]) (F fW ![s])) ∧
    F fD ![ns] = F (zArg fN fL) ![s] ∧ F fH ![ns] = 0 := by
  let ns := F (stepK .top true) ![s]
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
  have hn : F fN ![ns] = F (nextN fN fL) ![s] := by
    simp only [ns,stepK,pack_model,fN,fst_model,modelProjection,Matrix.cons_val_zero,pi₁_pair]
  have hl : F fL ![ns] = F (nextLA true fN fL) ![s] := by
    simp only [ns,stepK,pack_model,fL,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  have ht : F fT ![ns] = F (nextTopK .top true fN fL fT fW fD fH) ![s] := by
    simp only [ns,stepK,pack_model,fT,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  have hw : F fW ![ns] = F (nextStackK .top true fN fL fT fW fD fH) ![s] := by
    simp only [ns,stepK,pack_model,fW,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  have hd : F fD ![ns] = F (nextDK .top true fN fL fT fD fH) ![s] := by
    simp only [ns,stepK,pack_model,fD,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  have hh : F fH ![ns] = F (nextCacheK .top fN fL fT fW fD fH) ![s] := by
    simp only [ns,stepK,pack_model,fH,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  refine ⟨hn,?_,?_,?_,?_,?_⟩
  · rw [hl,nextLA,choose0_model,if_neg h0,choose1_model,if_neg h1]
  · rw [ht,nextTopK,choose0_model,if_neg h0,choose1_model,if_neg h1,axTopA]
    exact PRAMultiplication.modelZero _
  · rw [hw,nextStackK,choose0_model,if_neg h0,choose1_model,if_neg h1,axStackA,pair_model,axTop_model,axStack_model,harg]
  · rw [hd,nextDK,choose0_model,if_neg h0,choose1_model,if_neg h1,axDA,zField]
  · rw [hh,nextCacheK,choose0_model,if_neg h0,choose1_model,if_neg h1]
    exact PRAMultiplication.modelZero _
#print axioms nextFields
end models
end PA194AX11HAXSchedulerFields
