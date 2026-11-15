import PA194ControllerHaltReach
import PA194Site10Equivalence
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ActualControllerPhysicalConditional
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PA194FiniteControls PA194StateOne
open PA194SourceControllerCode PA194ControllerHaltReach PA194ActivePrefix PA194Site10Hit PA194Path27Header
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

/-- This is conditional on a model-uniform synchronization and the site-10
    tape representation. It does not establish either hypothesis. -/
theorem literalHaltIffControllerHalt
    (seed start : M) (hseed : F pc ![seed] < modelNumeral M 3673)
    (tape left suffix elapsed : M → M) (good : M → Prop)
    (hsync : ∀ i, F (active run (atSite10 pc)) ![i,seed] = 1 →
      good (F run ![i,seed]) ∧
      F PA194Stepper.stepper ![elapsed i,start] =
        F pairCode ![modelNumeral M 24,tape (F run ![i,seed])] ∧ i ≤ elapsed i)
    (htape : ∀ s, F pc ![s] = modelNumeral M 10 → tape s =
      F pairCode ![left s,modelWord (PA194SourceProgram.path 10) (suffix s)]) :
    (∃ t, ¬ pi₁ (F PA194Stepper.stepper ![t,start]) < modelNumeral M 194) ↔
      ∃ n, F pc ![F run ![n,seed]] = modelNumeral M 3674 := by
  exact (PA194Site10Equivalence.literalHaltIffSite10 run pc seed tape left suffix elapsed good start hsync htape).trans
    (reachesHaltIffSite10 seed hseed).symm
#print axioms literalHaltIffControllerHalt
end models
end PA194ActualControllerPhysicalConditional
