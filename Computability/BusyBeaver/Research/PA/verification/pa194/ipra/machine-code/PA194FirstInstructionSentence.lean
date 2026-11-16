import PA194FirstInstructionComplete
import PA194StartupSentence
import PA194StartupSourceFrame
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstInstructionSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open TableDispatch PA194StateOne PA194PackedNumeralBridge PA194StartupSentence

def firstInstructionClockBits : List Bool :=
  [false,false,false,true,true,true,true,true,false,false,true,false,false,true,true,true]
theorem firstInstructionClockBits_value : PA194Bounded.bits firstInstructionClockBits = 58616 := by decide +kernel

def lhs : TermN 0 := app2 PA194Stepper.stepper (bitsTerm firstInstructionClockBits) zero
def rhs : TermN 0 := pack (state 24) one (bitsTerm PA194FirstInstructionData.target.r)
def sentence : Sentence language := equalClosure lhs rhs

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local notation "F" => Structure.func (L := language)

/-- Fixed literal blank-to-site-27 run in every candidate PRA model; no
nonstandard-time simulation is claimed. -/
theorem modelBlankToSite27 :
    F PA194Stepper.stepper ![modelNumeral M 58616,modelNumeral M 0] =
    F pairCode ![modelNumeral M 24,
      F pairCode ![modelNumeral M 1,modelNumeral M (PA194Bounded.bits PA194FirstInstructionData.target.r)]] := by
  have hr : M6.Zip.run PA194.Literal.machine 58616 PA194Bounded.blankZip =
      some PA194FirstInstructionData.target := PA194FirstInstructionComplete.blankToSite27
  have h := literalBlankRun_explicitEndpoint (M := M) 58616 PA194FirstInstructionData.target hr
  have hl : PA194FirstInstructionData.target.l = [true] := by
    rw [←PA194FirstInstructionData.target_eq]
    rfl
  change F PA194Stepper.stepper ![modelNumeral M 58616,modelNumeral M 0] =
    F pairCode ![modelNumeral M 24,
      F pairCode ![modelNumeral M (PA194Bounded.bits PA194FirstInstructionData.target.l),
        modelNumeral M (PA194Bounded.bits PA194FirstInstructionData.target.r)]] at h
  rw [hl] at h
  exact h

theorem modelSentence : M↓[language] ⊧ sentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [lhs,rhs,PA194StartupSentence.pack,valApp2,valState,valOne,valZero,valBits,firstInstructionClockBits_value]
  rw [←modelNumeralOne]
  exact modelBlankToSite27 (M := M)
end models

theorem classicalPRA : PRA ⊢ sentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence

/-- Native intuitionistic PRA proves the exact fixed blank-to-site-27 equation. -/
theorem nativeIPRA : standardTheory ⊢ equalClosureI lhs rhs :=
  nativeOfClassical lhs rhs classicalPRA

#print axioms modelBlankToSite27
#print axioms modelSentence
#print axioms classicalPRA
#print axioms nativeIPRA
#print axioms PA194StartupSourceFrame.firstSeedSourceStep
end PA194FirstInstructionSentence
