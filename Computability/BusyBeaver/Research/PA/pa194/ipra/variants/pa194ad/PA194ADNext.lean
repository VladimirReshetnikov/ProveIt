import PA194ADDispatch
import ConfigurationStep
set_option autoImplicit false
namespace PA194ADNext
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASelectCode
open TableDispatch ConfigurationStep

def dest : Code 3 := app1 PA194ADDispatch.targetCode address
def nextQ : Code 3 := selectAmong live dest q

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelDest_eq (e : Fin 3 → M) (h : F address e < modelNumeral M 388)
    (h₁ : F address e ≠ modelNumeral M 219) (h₂ : F address e ≠ modelNumeral M 221)
    (h₃ : F address e ≠ modelNumeral M 249) :
    F dest e = F ConfigurationStep.dest e := by
  simp only [dest, ConfigurationStep.dest, modelApp1]
  exact PA194ADDispatch.modelTarget_eq_of_below _ h h₁ h₂ h₃

theorem modelNextQ_eq (e : Fin 3 → M) (h : F address e < modelNumeral M 388)
    (h₁ : F address e ≠ modelNumeral M 219) (h₂ : F address e ≠ modelNumeral M 221)
    (h₃ : F address e ≠ modelNumeral M 249) :
    F nextQ e = F ConfigurationStep.nextQ e := by
  simp only [nextQ, ConfigurationStep.nextQ, modelSelectAmong]
  rw [modelDest_eq e h h₁ h₂ h₃]

/-- Writes and tape movement use the same codes; under the row hypothesis,
all three components of the modeled configuration step agree. -/
theorem modelNext_eq (e : Fin 3 → M) (h : F address e < modelNumeral M 388)
    (h₁ : F address e ≠ modelNumeral M 219) (h₂ : F address e ≠ modelNumeral M 221)
    (h₃ : F address e ≠ modelNumeral M 249) :
    (F nextQ e, F ConfigurationStep.nextL e, F ConfigurationStep.nextR e) =
      (F ConfigurationStep.nextQ e, F ConfigurationStep.nextL e, F ConfigurationStep.nextR e) := by
  rw [modelNextQ_eq e h h₁ h₂ h₃]

#print axioms modelNext_eq
#print axioms modelDest_eq
#print axioms modelNextQ_eq
end models
end PA194ADNext
