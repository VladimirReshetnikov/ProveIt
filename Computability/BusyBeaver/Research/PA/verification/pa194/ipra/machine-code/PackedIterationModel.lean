import PackedDecoderModel

set_option autoImplicit false
/-! The explicit packed PA194 clock denotes an actual decoded configuration
run in every candidate PRA model, including at nonstandard model times. -/
namespace PackedIterationModel
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRASelectCode PRAIsZero PRAExhaustion PRAQOrder PRAModelIOpenPairing
open TableDispatch TableModelSemantics ConfigurationStep PackedClock PackedRootModel PackedDecoderModel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelInject (f : Code 3) (x : M) :
    F (inject3 f) (fun _ => x) = F f ![F packedQ (fun _ => x), F packedL (fun _ => x), F packedR (fun _ => x)] := by
  rw [inject3, modelComposition]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  exact Fin.cases rfl (fun l => Fin.elim0 l) k

theorem modelEncodedStepAny (x : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    F encodedStep (fun _ => x) =
      let c := stepSem (pi₁ x) (pi₁ (pi₂ x)) (pi₂ (pi₂ x))
      F pairCode ![c.1, F pairCode ![c.2.1,c.2.2]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [encodedStep, modelBin, modelInject, packedQ, packedL, packedR,
    modelUnary, modelDecodeLeft, modelDecodeRight]
  have hn := modelNext (![pi₁ x, pi₁ (pi₂ x), pi₂ (pi₂ x)] : Fin 3 → M)
  change (F nextQ ![pi₁ x,pi₁ (pi₂ x),pi₂ (pi₂ x)],
    F nextL ![pi₁ x,pi₁ (pi₂ x),pi₂ (pi₂ x)],
    F nextR ![pi₁ x,pi₁ (pi₂ x),pi₂ (pi₂ x)]) = _ at hn
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hn
  change (F nextQ ![pi₁ x,pi₁ (pi₂ x),pi₂ (pi₂ x)],
    F nextL ![pi₁ x,pi₁ (pi₂ x),pi₂ (pi₂ x)],
    F nextR ![pi₁ x,pi₁ (pi₂ x),pi₂ (pi₂ x)]) = stepSem (pi₁ x) (pi₁ (pi₂ x)) (pi₂ (pi₂ x)) at hn
  cases h : stepSem (pi₁ x) (pi₁ (pi₂ x)) (pi₂ (pi₂ x)) with
  | mk a bc =>
    cases bc with
    | mk b c =>
      rw [h] at hn
      simp only [Prod.mk.injEq] at hn
      rw [hn.1,hn.2.1,hn.2.2]


/-- The decoded initial clock is the blank start configuration. -/
theorem modelClockDecodedZero :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    let n := F clock (fun _ => (0 : M))
    (F decodeLeft (fun _ => n), F decodeLeft (fun _ => F decodeRight (fun _ => n)),
      F decodeRight (fun _ => F decodeRight (fun _ => n))) = ((0 : M),0,0) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hp : pair (0 : M) 0 = 0 := by simp [pair]
  have hl : pi₁ (0 : M) = 0 := by simpa [hp] using pi₁_pair (0 : M) 0
  have hr : pi₂ (0 : M) = 0 := by simpa [hp] using pi₂_pair (0 : M) 0
  dsimp only
  have hz : F clock (fun _ => (0 : M)) = (0 : M) := modelClockZero
  rw [hz]
  simp only [modelDecodeLeft, modelDecodeRight, hl, hr]

/-- The decoded clock really performs a configuration step at every model
time, including nonstandard elements; no external induction on the time is used. -/
theorem modelClockDecodedSucc (t : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    let n := F clock (fun _ => t)
    let n' := F clock (fun _ => F Code.succ (fun _ => t))
    (F decodeLeft (fun _ => n'),
      F decodeLeft (fun _ => F decodeRight (fun _ => n')),
      F decodeRight (fun _ => F decodeRight (fun _ => n'))) =
        stepSem (pi₁ n) (pi₁ (pi₂ n)) (pi₂ (pi₂ n)) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  rw [modelClockSucc, modelEncodedStepAny]
  simp only [modelDecodeLeft, modelDecodeRight, modelPairCode, pi₁_pair, pi₂_pair]

/-- The explicit indicator is one exactly when the decoded control is no
longer a working control, uniformly even at nonstandard model times. -/
theorem modelHaltIndicator (t : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    F haltIndicator (fun _ => t) = (1 : M) ↔
      ¬ pi₁ (F clock (fun _ => t)) < modelNumeral M 194 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [haltIndicator, clockState, const194, modelUnary, modelBin,
    modelConstant, modelDecodeLeft]
  have hi := modelIsZeroCharacter (F ltBitCode ![pi₁ (F clock (fun _ => t)), modelNumeral M 194])
  have hz := modelLtZero (pi₁ (F clock (fun _ => t))) (modelNumeral M 194)
  exact hi.trans hz

#print axioms modelHaltIndicator

#print axioms modelClockDecodedZero
#print axioms modelClockDecodedSucc

#print axioms modelEncodedStepAny
end models
end PackedIterationModel
