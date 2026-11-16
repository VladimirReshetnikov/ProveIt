import PA194Site10Hit
import PA194RootFrameNonhalt
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site10Equivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PA194Stepper PA194StepperCompose
open PA194ControllerHalt PA194Path27Header PA194GatedActiveHit PA194ActivePrefix
open TableDispatch PRAEqualityCode PRABooleanOps PA194CumulativeClock PA194HaltPathSegment PA194Site10Hit PA194RootFrameNonhalt

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
/-- Literal halt and site-10 hit are equivalent for any run/PC codes satisfying
    the explicit gated synchronization and PC/frame representation. -/
theorem literalHaltIffSite10
    (run : Code 2) (pc : Code 1) (seed : M)
    (tape left suffix elapsed : M → M) (good : M → Prop) (start : M)
    (hsync : ∀ i, F (active run (atSite10 pc)) ![i,seed] = 1 →
      good (F run ![i,seed]) ∧
      F stepper ![elapsed i,start] = F pairCode ![modelNumeral M 24,tape (F run ![i,seed])] ∧
      i ≤ elapsed i)
    (htape : ∀ s, F pc ![s] = modelNumeral M 10 → tape s =
      F pairCode ![left s,modelWord (PA194SourceProgram.path 10) (suffix s)]) :
    (∃ t, ¬ pi₁ (F stepper ![t,start]) < modelNumeral M 194) ↔
      ∃ n, F pc ![F run ![n,seed]] = modelNumeral M 10 := by
  constructor
  · rintro ⟨t,ht⟩
    obtain ⟨i,_,hi⟩ := haltImpliesCodeHit run (atSite10 pc) seed tape elapsed good start t hsync ht
    exact ⟨i,(atSite10Model pc _).mp hi⟩
  · rintro ⟨n,hn⟩
    obtain ⟨i,_,hi⟩ := site10ReachesLiteralHalt run pc seed tape left suffix elapsed good start n hsync htape hn
    exact ⟨F addCode ![elapsed i,modelNumeral M 3],hi⟩
#print axioms literalHaltIffSite10
end models
end PA194Site10Equivalence
