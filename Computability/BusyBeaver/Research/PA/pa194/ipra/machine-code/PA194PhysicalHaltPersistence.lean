import PA194GatedModelLength
import PA194ClockInvariantDefinable
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194PhysicalHaltPersistence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PA194Stepper PA194StepperCompose PA194ClockInvariantDefinable PA194GatedModelLength PackedClock PackedIterationModel PackedDecoderModel TableDispatch TableModelSemantics PRAQOrder PRAExhaustion PackedRootModel ConfigurationStep
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



/-- Once the packed control is at least 194, the totalized literal step is a fixed point. -/
theorem encodedHaltFixed (x : M) (h : ¬ pi₁ x < modelNumeral M 194) :
    F encodedStep (fun _ => x) = x := by
  have hz := (modelLtZero (pi₁ x) (modelNumeral M 194)).mpr h
  change F ltBitCode ![pi₁ x,modelNumeral M 194] = F (Code.zero 0) Fin.elim0 at hz
  rw [modelEncodedStepAny]
  simp only [stepSem,hz,if_true,modelPairCode]
  rw [pair_unpair, pair_unpair]

theorem haltedStepperFixed (x : M) (h : ¬ pi₁ x < modelNumeral M 194) :
    ∀ k : M, F stepper ![k,x] = x := by
  have hf : 𝚺₁-Function₁ (fun k : M => F stepper ![k,x]) :=
    bindBinary _ x (binaryCodeDef (M := M) stepper)
  haveI := hf
  have hd : 𝚺₁-Predicate (fun k : M => F stepper ![k,x] = x) := by definability
  intro k
  induction k using ISigma1.sigma1_succ_induction with
  | hP => exact hd
  | zero => exact modelStepperZero x
  | succ k ih =>
    change F stepper ![F addCode ![k,F oneCode Fin.elim0],x] = x
    rw [modelAddOne]
    rw [modelStepperSucc, ih, encodedHaltFixed x h]

theorem haltPersists (start t u : M) (htu : t ≤ u)
    (h : ¬ pi₁ (F stepper ![t,start]) < modelNumeral M 194) :
    ¬ pi₁ (F stepper ![u,start]) < modelNumeral M 194 := by
  obtain ⟨d, hd⟩ := exists_add_of_le htu
  rw [hd]
  change ¬ pi₁ (F stepper ![F addCode ![t,d],start]) < modelNumeral M 194
  rw [modelStepperCompose, haltedStepperFixed _ h]
  exact h
#print axioms haltPersists
#print axioms haltedStepperFixed
#print axioms encodedHaltFixed
end models
end PA194PhysicalHaltPersistence
