import PA194SourceSite28DynamicPhysical
import PA194SourceSite29DynamicPhysical
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceSite28Then29Dynamic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourceRegisterRelation PA194SourceSite25Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem twoSteps (k tail count : M) (args : Fin 11 → M)
    (htail : args 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)]) :
    let mid := PA194Site28DynamicOutput.updated args count
    let out := PA194Site29DynamicOutput.updated mid (count+1)
    ∃ c1 c2 : M,
      F step ![F step ![sourceState 28 args tail]] = sourceState 30 out tail ∧
      F PA194Stepper.stepper ![c2,F PA194Stepper.stepper ![c1,physicalFrame 28 (((k+1)+1)+1) args]] =
        physicalFrame 30 ((k+1)+1) out := by
  let mid := PA194Site28DynamicOutput.updated args count
  let out := PA194Site29DynamicOutput.updated mid (count+1)
  have hmid : mid 10 = F PA194OneSpareReturn.repeatOutput ![count+1,(0 : M)] := by
    simp [mid,PA194Site28DynamicOutput.updated,←modelAddOne]
    rfl
  obtain ⟨h28,c1,hp28⟩ := PA194SourceSite28DynamicPhysical.sourcePhysical (k+1) tail count args htail
  obtain ⟨h29,c2,hp29⟩ := PA194SourceSite29DynamicPhysical.sourcePhysical k tail (count+1) mid hmid
  refine ⟨c1,c2,?_,?_⟩
  · rw [h28,h29]
  · rw [hp28,hp29]
#print axioms twoSteps
end models
end PA194SourceSite28Then29Dynamic
