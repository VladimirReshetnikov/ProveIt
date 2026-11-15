import PA194SchedulerFetchPositive
import PA194SchedulerIteration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SchedulerPackedFetchPositive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SchedulerCode PA194SchedulerIteration PA194SchedulerFetchPositive
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

theorem packedNextN (s : M) :
    F fN ![F PA194SchedulerIteration.step ![s]] = F (nextN fN fL) ![s] := by
  simp only [fN,fst_model,PA194SchedulerIteration.step,pack_model,modelProjection,Matrix.cons_val_zero,pi₁_pair]

theorem packedPositiveFields (s n m : M) (hn : F fN ![s] = n) (hl : F fL ![s] = m+1) :
    F (fetchSeed fN fL) ![s] = m ∧ F fN ![F PA194SchedulerIteration.step ![s]] = n := by
  have hp : m+1 ≠ (0 : M) := ne_of_gt (lt_of_le_of_lt (zero_le : (0 : M) ≤ m)
    (lt_add_of_pos_right m (Arithmetic.zero_lt_one : (0 : M) < 1)))
  constructor
  · rw [fetchSeed,choose0_model,hl,if_neg hp,PA194PathIterator.modelUnary,hl]
    change F predCode (fun _ => m+1) = m
    rw [show m+1 = F Code.succ (fun _ => m) from modelAddOne m,modelPredSucc]
  · rw [packedNextN,nextN,choose0_model,hl,if_neg hp,hn]

theorem packedPositiveFetchPrefix (s : M) (args : Fin 11 → M) (tail m : M)
    (hn : F fN ![s] = args 0) (hl : F fL ![s] = args 8) (hm : args 8=m+1) :
    F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![sourceState 25 args tail]] =
      sourceState 34 (Function.update args 8 m) tail ∧
    F (fetchSeed fN fL) ![s] = m ∧ F fN ![F PA194SchedulerIteration.step ![s]] = args 0 := by
  refine ⟨(positiveFetchPrefix args tail m hm).1,?_⟩
  exact packedPositiveFields s (args 0) m hn (hl.trans hm)
#print axioms packedNextN
#print axioms packedPositiveFields
#print axioms packedPositiveFetchPrefix
end models
end PA194SchedulerPackedFetchPositive
