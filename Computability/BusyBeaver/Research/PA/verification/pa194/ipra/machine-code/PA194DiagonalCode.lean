import PA194UnpairCantor
import PA194IteratedSimulation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194DiagonalCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASubtraction
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch PackedClock PackedRootModel PackedDecoderModel
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SchedulerCode PA194TargetCantor PA194MachineProjections PA194IteratedSimulation
noncomputable def nextX : Code 1 := choose0 decodeLeft (unary Code.succ decodeRight) (unary predCode decodeLeft)
noncomputable def nextY : Code 1 := choose0 decodeLeft (.zero 1) (unary Code.succ decodeRight)
noncomputable def next : Code 1 := bin pairCode nextX nextY
noncomputable def run : Code 2 := iterate next
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem nextZero (b : M) : F next ![pair (0 : M) b] = pair (b+1) (0 : M) := by
  have hv : (![pair (0 : M) b] : Fin 1 → M) = (fun _ => pair (0 : M) b) := by
    funext i; fin_cases i; rfl
  rw [hv]
  simp only [next,modelBin,modelPairCode,nextX,nextY,choose0_model,modelUnary,
    modelDecodeLeft,modelDecodeRight,pi₁_pair,pi₂_pair,if_true,PRAMultiplication.modelZero,←modelAddOne]
  rfl

theorem nextPositive (a b : M) : F next ![pair (a+1) b] = pair a (b+1) := by
  have hn : a+1 ≠ (0 : M) := ne_of_gt (lt_of_le_of_lt (zero_le : (0 : M) ≤ a) (lt_add_one a))
  have hv : (![pair (a+1) b] : Fin 1 → M) = (fun _ => pair (a+1) b) := by
    funext i; fin_cases i; rfl
  rw [hv]
  simp only [next,modelBin,modelPairCode,nextX,nextY,choose0_model,modelUnary,
    modelDecodeLeft,modelDecodeRight,pi₁_pair,pi₂_pair,if_neg hn,←modelAddOne]
  rw [show a+1 = F Code.succ (fun _ => a) from modelAddOne a,modelPredSucc]
  rfl
theorem nextEq (s : M) : F next ![s] =
    if pi₁ s = (0 : M) then pair (pi₂ s+1) (0 : M)
    else pair (F predCode (fun _ => pi₁ s)) (pi₂ s+1) := by
  have hv : (![s] : Fin 1 → M) = (fun _ => s) := by funext i; fin_cases i; rfl
  rw [hv]
  simp only [next,modelBin,modelPairCode,nextX,nextY,choose0_model,modelUnary,
    modelDecodeLeft,modelDecodeRight,PRAMultiplication.modelZero,←modelAddOne]
  by_cases h : pi₁ s = (0 : M) <;> simp only [h,if_true,if_false]
  all_goals rfl

theorem scoreNext (s : M) :
    cantor (pi₁ (F next ![s])) (pi₂ (F next ![s])) = cantor (pi₁ s) (pi₂ s)+1 := by
  rw [nextEq]
  by_cases hx : pi₁ s = (0 : M)
  · simp only [hx,if_true,pi₁_pair,pi₂_pair]
    have h := PA194UnpairCantor.zeroCantor (pi₂ s) (0 : M)
    simpa only [add_zero,zero_add] using h
  · have hp : (0 : M) < pi₁ s := lt_of_le_of_ne (zero_le : (0 : M) ≤ pi₁ s) (Ne.symm hx)
    have hle : (1 : M) ≤ pi₁ s := by simpa using (lt_iff_succ_le.mp hp)
    obtain ⟨a,ha⟩ := le_iff_exists_add.mp hle
    have he : pi₁ s = a+1 := by simpa [add_comm] using ha
    simp only [hx,if_false,pi₁_pair,pi₂_pair]
    rw [he,show a+1 = F Code.succ (fun _ => a) from modelAddOne a,modelPredSucc,←modelAddOne]
    change cantor a (pi₂ s+1) = cantor (a+1) (pi₂ s)+1
    have h := PA194UnpairCantor.positiveCantor a (pi₂ s) (0 : M)
    simpa only [add_zero,zero_add] using h
#print axioms nextEq
#print axioms scoreNext
#print axioms nextZero
#print axioms nextPositive
end models
end PA194DiagonalCode
