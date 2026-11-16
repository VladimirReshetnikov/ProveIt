import PA194SourceDynamicLoop
import PA194TransferMacroWidths
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace PA194Width57Growth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ModelLoopIteration PA194RegisterPermutation PA194ActualLoopOrbit PA194SourceSite31Physical PA194StateOne PA194FiniteControls TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem width57Loop (tail count m : M) (args : Fin 11 → M)
    (hm : args 0 = m+1)
    (ht : args 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)]) :
    let mid := PA194Site28DynamicOutput.updated (Function.update args 0 m) count
    let out := PA194Site29DynamicOutput.updated mid (count+1)
    ∃ c0 c1 c2 : M,
      F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![
        F PA194SourceControllerCode.step ![PA194SourceSite31Controller.sourceState 27 args tail]]]] =
        PA194SourceSite31Controller.sourceState 27 out tail ∧
      F PA194Stepper.stepper ![modelNumeral M 40,F PA194Stepper.stepper ![c2,
        F PA194Stepper.stepper ![c1,F PA194Stepper.stepper ![c0,
          physicalFrame 27 (((modelNumeral M 47+1)+1)+1) args]]]] =
        physicalFrame 27 ((((modelNumeral M 47+1)+1)+1)+1) out ∧
      PA194TransferMacroWidths.width 27 (((modelNumeral M 47+1)+1)+1) = modelNumeral M 57 ∧
      PA194TransferMacroWidths.width 27 ((((modelNumeral M 47+1)+1)+1)+1) = modelNumeral M 58 := by
  have hpath : (PA194SourceProgram.path 27).length = 7 := by decide +kernel
  obtain ⟨c0,c1,c2,hs,hp⟩ := PA194SourceDynamicLoop.fourSteps (modelNumeral M 47) tail count m args hm ht
  refine ⟨c0,c1,c2,hs,hp,?_,?_⟩
  · simp only [PA194TransferMacroWidths.width,hpath]
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd]
  · simp only [PA194TransferMacroWidths.width,hpath]
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd]
#print axioms width57Loop
end models
end PA194Width57Growth
