import PA194SeedToFirstSite36
import PA194Site36ZeroRun
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194SeedToFirstSite38
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194SeedToFirstSite35 PA194SeedToFirstSite36 PA194SourceSite31Physical PA194StateOne PA194FiniteControls TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem blankTo38 (tail : M) :
    ∃ c0 c1 c2 c3 : M,
      PA194Site36ZeroRun.run (modelNumeral M 40) (args36 (M := M))
        (PA194Site35Run.run (modelNumeral M 42) (count35 (M := M)) (next35 (M := M))
          (F PA194Stepper.stepper ![c3,F PA194Stepper.stepper ![c2,F PA194Stepper.stepper ![c1,F PA194Stepper.stepper ![c0,modelNumeral M 0]]]])) =
        physicalFrame 38 (modelNumeral M 42) (args36 (M := M)) := by
  obtain ⟨c0,c1,c2,c3,h36⟩ := blankTo36 (M := M) tail
  have h38 := PA194Site36ZeroRun.correct (modelNumeral M 40) (args36 (M := M)) (reg6Zero (M := M))
  have hgap : (modelNumeral M 40+1)+1 = modelNumeral M 42 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  rw [hgap] at h38
  refine ⟨c0,c1,c2,c3,?_⟩
  rw [h36]
  exact h38
#print axioms blankTo38
end models
end PA194SeedToFirstSite38
