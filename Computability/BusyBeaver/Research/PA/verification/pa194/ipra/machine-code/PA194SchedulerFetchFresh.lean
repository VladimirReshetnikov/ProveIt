import PA194SchedulerPackedFetchPositive
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SchedulerFetchFresh
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters PA194SourceRegisterRelation PA194SourcePCBound
open PA194SchedulerCode PA194SchedulerIteration PA194SchedulerFetchPositive PA194SchedulerPackedFetchPositive
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem sourceZero25 (args : Fin 11 → M) (tail : M) (hz : args 8 = (0 : M)) :
    F PA194SourceControllerCode.step ![sourceState 25 args tail] = sourceState 27 args tail := by
  have hpc : F pc ![sourceState 25 args tail] = modelNumeral M 25 := by
    rw [pcModel]; exact pi₁_pair _ _
  have hreg : getSem 8 (pi₂ (sourceState 25 args tail)) = args 8 := by
    change getSem 8 (pi₂ (pair (modelNumeral M 25) (pack (regsOfArgs args) tail))) = args 8
    rw [pi₂_pair]
    have h := packEncodes (regsOfArgs args) tail (8 : Fin 9)
    change getSem 8 (pack (regsOfArgs args) tail) = args 8 at h
    exact h
  rw [site25Zero _ hpc (hreg.trans hz)]
  change pair (modelNumeral M 27) (pi₂ (pair (modelNumeral M 25) (pack (regsOfArgs args) tail))) = _
  rw [pi₂_pair]
  rfl

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem freshFields (s n : M) (hn : F fN ![s] = n) (hl : F fL ![s] = (0 : M)) :
    F (fetchSeed fN fL) ![s] = n ∧ F fN ![F PA194SchedulerIteration.step ![s]] = n+1 := by
  constructor
  · rw [fetchSeed,choose0_model,hl,if_pos rfl,hn]
  · rw [packedNextN,nextN,choose0_model,hl,if_pos rfl,PA194PathIterator.modelUnary,hn]
    exact modelAddOne n |>.symm

theorem freshFetchPrefix (s : M) (args : Fin 11 → M) (tail : M)
    (hn : F fN ![s] = args 0) (hl : F fL ![s] = args 8) (hz : args 8=(0 : M)) :
    F PA194SourceControllerCode.step ![sourceState 25 args tail] = sourceState 27 args tail ∧
    F (fetchSeed fN fL) ![s] = args 0 ∧
    F fN ![F PA194SchedulerIteration.step ![s]] = args 0+1 := by
  exact ⟨sourceZero25 args tail hz,freshFields s (args 0) hn (hl.trans hz)⟩
#print axioms sourceZero25
#print axioms freshFields
#print axioms freshFetchPrefix
end models
end PA194SchedulerFetchFresh
