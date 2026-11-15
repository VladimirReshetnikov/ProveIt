import PA194SchedulerFetchPositive
import PA194SchedulerIteration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SchedulerFieldsOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SchedulerCode PA194SchedulerIteration PA194SchedulerFetchPositive
open PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194NumeralCode PA194TargetCantor
 PA194TargetStep PA194TargetExtendedStep PA194MachineProjections PA194MachineStack PA194MachineAXCode
 PA194MachineShiftMPCode PA194StackCode PA194BranchSeed PA194TargetProofLeaf
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem fstModel {m : Nat} (a : Code m) (e : Fin m → M) : F (fst a) e = π₁ (F a e) := by
  rw [fst,PA194PathIterator.modelUnary,modelPi1Code firstProjection firstProjection_certified]
theorem packModel {m : Nat} (n l t w d h : Code m) (e : Fin m → M) :
    F (pack n l t w d h) e = pair (F n e) (pair (F l e) (pair (F t e) (pair (F w e) (pair (F d e) (F h e))))) := by
  simp only [PA194SchedulerIteration.pack,modelBin,modelPairCode]
theorem packedNextN (s : M) :
    F fN ![F PA194SchedulerIteration.step ![s]] = F (nextN fN fL) ![s] := by
  simp only [fN,fstModel,PA194SchedulerIteration.step,packModel,modelProjection,Matrix.cons_val_zero,pi₁_pair]

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
theorem freshFields (s n : M) (hn : F fN ![s] = n) (hl : F fL ![s] = (0 : M)) :
    F (fetchSeed fN fL) ![s] = n ∧ F fN ![F PA194SchedulerIteration.step ![s]] = n+1 := by
  constructor
  · rw [fetchSeed,choose0_model,hl,if_pos rfl,hn]
  · rw [packedNextN,nextN,choose0_model,hl,if_pos rfl,PA194PathIterator.modelUnary,hn]
    exact modelAddOne n |>.symm
#print axioms freshFields
#print axioms packedNextN
#print axioms packedPositiveFields
#print axioms packedPositiveFetchPrefix
end models
end PA194SchedulerFieldsOpen
