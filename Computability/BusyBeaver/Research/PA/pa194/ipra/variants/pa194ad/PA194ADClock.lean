import PA194ADNext
import PackedIterationModel
import DiophantineConsistency.IPRAPA196Consistency
import DiophantineConsistency.IPRANativeFormulaRew
set_option autoImplicit false
namespace PA194ADClock
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAIsZero PRASelectCode PackedClock PackedIterationModel TableDispatch
open IPRANativeFormula

def encodedStep : Code 1 := bin pairCode (inject3 PA194ADNext.nextQ)
  (bin pairCode (inject3 ConfigurationStep.nextL) (inject3 ConfigurationStep.nextR))
def clockStep : Code 2 := unary encodedStep (.proj 1)
def clock : Code 1 := .prec (.zero 0) clockStep
def clockState : Code 1 := unary decodeLeft clock
def haltIndicator : Code 1 := unary isZeroCode (bin ltBitCode clockState const194)
def haltTerm : Semiterm language Empty 1 := .func haltIndicator (fun _ => #0)
def haltMatrix : Semisentence language 1 := .rel .eq ![haltTerm, .func oneCode Fin.elim0]
def haltClassical : Sentence language := ∃⁰ haltMatrix
def haltSentence : Sentenceᵢ language := native haltClassical

theorem haltMatrix_bounded : Hierarchy 𝚺 0 haltMatrix := Hierarchy.rel _ _ _ _

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelEncodedStep_eq (x : M)
    (h : F ConfigurationStep.address ![F packedQ (fun _ => x), F packedL (fun _ => x), F packedR (fun _ => x)] < modelNumeral M 388)
    (h₁ : F ConfigurationStep.address ![F packedQ (fun _ => x), F packedL (fun _ => x), F packedR (fun _ => x)] ≠ modelNumeral M 219)
    (h₂ : F ConfigurationStep.address ![F packedQ (fun _ => x), F packedL (fun _ => x), F packedR (fun _ => x)] ≠ modelNumeral M 221)
    (h₃ : F ConfigurationStep.address ![F packedQ (fun _ => x), F packedL (fun _ => x), F packedR (fun _ => x)] ≠ modelNumeral M 249) :
    F encodedStep (fun _ => x) = F PackedClock.encodedStep (fun _ => x) := by
  simp only [encodedStep, PackedClock.encodedStep, modelBin, modelInject]
  rw [PA194ADNext.modelNextQ_eq _ h h₁ h₂ h₃]

#print axioms modelEncodedStep_eq
end models
#print axioms haltMatrix_bounded
end PA194ADClock
