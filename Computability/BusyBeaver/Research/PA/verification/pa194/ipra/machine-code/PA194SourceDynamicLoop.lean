import PA194SourceSite28Then29Dynamic
import PA194SourceSite27Physical
import PA194SourceSite30Physical
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceDynamicLoop
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

theorem fourSteps (k tail count m : M) (args : Fin 11 → M)
    (hm : args 0 = m+1)
    (htail : args 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)]) :
    let start28 := Function.update args 0 m
    let mid := PA194Site28DynamicOutput.updated start28 count
    let out := PA194Site29DynamicOutput.updated mid (count+1)
    ∃ c0 c1 c2 : M,
      F step ![F step ![F step ![F step ![sourceState 27 args tail]]]] = sourceState 27 out tail ∧
      F PA194Stepper.stepper ![modelNumeral M 40,F PA194Stepper.stepper ![c2,
        F PA194Stepper.stepper ![c1,F PA194Stepper.stepper ![c0,
          physicalFrame 27 (((k+1)+1)+1) args]]]] =
        physicalFrame 27 ((((k+1)+1)+1)+1) out := by
  let start28 := Function.update args 0 m
  let mid := PA194Site28DynamicOutput.updated start28 count
  let out := PA194Site29DynamicOutput.updated mid (count+1)
  have htail28 : start28 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)] := by simp [start28,htail]
  obtain ⟨h27,c0,hp27⟩ := PA194SourceSite27Physical.positiveBranch (k+1) tail m args hm
  obtain ⟨c1,c2,h2829,hp2829⟩ := PA194SourceSite28Then29Dynamic.twoSteps k tail count start28 htail28
  obtain ⟨h30,hp30⟩ := PA194SourceSite30Physical.sourcePhysical k tail out
  refine ⟨c0,c1,c2,?_,?_⟩
  · rw [h27,h2829,h30]
  · rw [hp27,hp2829,hp30]
#print axioms fourSteps
end models
end PA194SourceDynamicLoop
