import PA194RestorePhysicalFrame
import PA194Site31TransferClockCode
import PA194ModelLoopCost
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194RestorePhysicalCost
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopCost PA194ControllerLoopFrame PA194OneSpareReturn PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls PA194RegisterFile PA194RegisterPermutation PA194Path27Header BinaryTapeCodes PackedDecoderModel TableDispatch

def k31 : Code 1 := prev (prev gap)
def k32 : Code 1 := prev k31
def inputs : Fin 14 → Code 1 := ![reg readers 0,reg readers 1,reg readers 2,reg readers 3,reg readers 4,
  reg readers 5,reg readers 6,reg readers 7,reg readers 8,.zero 1,k31,count,spare,k32]
def cost : Code 1 := applyCodes PA194Site31TransferClockCode.clockCode inputs
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelCost (r : Fin 9 → M) (tail k n s : M) :
    let x := packed (((k+1)+1)+1) n s (PA194ModelRestoreSource.source r tail)
    F cost (fun _ => x) = F PA194Site31TransferClockCode.clockCode
      ![r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8,(0 : M),k+1,n,s,k] := by
  dsimp only
  let x := packed (((k+1)+1)+1) n s (PA194ModelRestoreSource.source r tail)
  have hg : F gap (fun _ => x) = ((k+1)+1)+1 := by
    simp [gap,x,packed,modelDecodeLeft,modelPairCode,pi₁_pair]
  have hn : F count (fun _ => x) = n := by
    simp [count,rest,x,packed,modelUnary,modelProjection,modelDecodeLeft,modelDecodeRight,modelPairCode,pi₁_pair,pi₂_pair]
  have hs : F spare (fun _ => x) = s := by
    simp [PA194ModelLoopState.spare,rest,rest2,x,packed,modelUnary,modelProjection,modelDecodeLeft,modelDecodeRight,modelPairCode,pi₁_pair,pi₂_pair]
  have hr (i : Fin 9) : F (reg readers i) (fun _ => x) = r i := by
    simp only [reg,modelUnary,PA194ModelLoopState.control,rest,rest2,x,packed,modelProjection,modelDecodeRight,modelPairCode,pi₂_pair]
    exact PA194RestorePhysicalFrame.readSource r tail i
  have hk31 : F k31 (fun _ => x) = k+1 := by
    simp only [k31,prev,modelUnary,hg]
    rw [show ((k+1)+1)+1 = F Code.succ (fun _ => (k+1)+1) from modelAddOne _,modelPredSucc,
      show (k+1)+1 = F Code.succ (fun _ => k+1) from modelAddOne _,modelPredSucc]
  have hk32 : F k32 (fun _ => x) = k := by
    simp only [k32,prev,modelUnary,hk31]
    rw [show k+1 = F Code.succ (fun _ => k) from modelAddOne _,modelPredSucc]
  dsimp only [x] at hr hg hn hs hk31 hk32
  rw [cost,modelApplyCodes]
  congr 1
  funext i
  fin_cases i <;> simp [inputs,hr,hk31,hk32,hn,hs,PRAMultiplication.modelZero] <;> rfl
#print axioms modelCost
end models
end PA194RestorePhysicalCost
