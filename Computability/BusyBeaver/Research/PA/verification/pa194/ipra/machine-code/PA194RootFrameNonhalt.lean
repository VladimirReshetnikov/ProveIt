import PA194PhysicalHaltPersistence
import PA194FiniteControls
import PA194GatedActiveHit
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194RootFrameNonhalt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PA194Stepper PA194StepperCompose PA194ClockInvariantDefinable PA194GatedModelLength PackedClock PackedIterationModel PackedDecoderModel TableDispatch TableModelSemantics PRAQOrder PRAExhaustion PackedRootModel ConfigurationStep PA194GatedActiveHit PA194PhysicalHaltPersistence
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




theorem numeralCast (n : Nat) : modelNumeral M n = (n : M) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [PA194FiniteControls.modelNumeralSucc, ih]
    simp

/-- Any packed state-24 root frame is a nonhalting literal configuration,
    regardless of the encoded tape. -/
theorem rootFrameNonhalt (tape : M) :
    pi₁ (F pairCode ![modelNumeral M 24,tape]) < modelNumeral M 194 := by
  rw [modelPairCode,pi₁_pair,numeralCast,numeralCast]
  norm_num
/-- A physical halt implies a bounded PR hit, assuming only the stated
    synchronization with state-24 root frames. -/
theorem haltImpliesCodeHit
    (run : Code 2) (hit : Code 1) (seed : M)
    (tape elapsed : M → M) (good : M → Prop) (start t : M)
    (hsync : ∀ n, F (PA194ActivePrefix.active run hit) ![n,seed] = 1 →
      good (F run ![n,seed]) ∧
      F stepper ![elapsed n,start] =
        F pairCode ![modelNumeral M 24,tape (F run ![n,seed])] ∧ n ≤ elapsed n)
    (hh : ¬ pi₁ (F stepper ![t,start]) < modelNumeral M 194) :
    ∃ i, i ≤ t ∧ F hit ![F run ![i,seed]] ≠ 0 := by
  apply haltToCodeHit run hit seed
    (fun s => F pairCode ![modelNumeral M 24,tape s]) elapsed good
    (fun x => ¬ pi₁ x < modelNumeral M 194) start hsync (haltPersists start) _ t hh
  intro s _ h
  exact h (rootFrameNonhalt (tape s))
#print axioms haltImpliesCodeHit
#print axioms rootFrameNonhalt
end models
end PA194RootFrameNonhalt
