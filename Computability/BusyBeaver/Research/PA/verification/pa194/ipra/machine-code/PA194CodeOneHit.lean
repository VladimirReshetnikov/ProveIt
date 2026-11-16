import PA194RootFrameNonhalt
import DiophantineConsistency.PRAEqualityCode
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194CodeOneHit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PA194Stepper PA194StepperCompose PA194ClockInvariantDefinable PA194GatedModelLength PackedClock PackedIterationModel PackedDecoderModel TableDispatch TableModelSemantics PRAQOrder PRAExhaustion PackedRootModel ConfigurationStep PA194GatedActiveHit PA194PhysicalHaltPersistence PRAEqualityCode PRABooleanOps PA194CumulativeClock
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





def equalsOne (hit : Code 1) : Code 1 :=
  bin equalityCode hit (.comp oneCode (.nil 1))

theorem equalsOneModel (hit : Code 1) (x : M) :
    F (equalsOne hit) ![x] ≠ 0 ↔ F hit ![x] = 1 := by
  rw [equalsOne,modelBin,modelComposition]
  have hnil : (fun i : Fin 0 => F (getCode (Codes.nil 1) i) ![x]) = Fin.elim0 := Subsingleton.elim _ _
  rw [hnil]
  have ⟨hb,hc⟩ := modelEqualityCode (F hit ![x]) (1 : M)
  change (F equalityCode ![F hit ![x], (1 : M)] ≠ 0) ↔ _
  constructor
  · intro hn
    have he : F equalityCode ![F hit ![x], (1 : M)] = 1 := hb.resolve_left hn
    exact hc.mp he
  · intro he hz
    have ho := hc.mpr he
    rw [hz] at ho
    exact (ne_of_lt (Arithmetic.zero_lt_one : (0 : M) < 1)) ho
theorem haltImpliesCodeOne
    (run : Code 2) (hit : Code 1) (seed : M)
    (tape elapsed : M → M) (good : M → Prop) (start t : M)
    (hsync : ∀ n, F (PA194ActivePrefix.active run (equalsOne hit)) ![n,seed] = 1 →
      good (F run ![n,seed]) ∧
      F stepper ![elapsed n,start] =
        F pairCode ![modelNumeral M 24,tape (F run ![n,seed])] ∧ n ≤ elapsed n)
    (hh : ¬ pi₁ (F stepper ![t,start]) < modelNumeral M 194) :
    ∃ i, i ≤ t ∧ F hit ![F run ![i,seed]] = 1 := by
  obtain ⟨i,hi,hitone⟩ := PA194RootFrameNonhalt.haltImpliesCodeHit
    run (equalsOne hit) seed tape elapsed good start t hsync hh
  exact ⟨i,hi,(equalsOneModel hit _).mp hitone⟩
#print axioms haltImpliesCodeOne
#print axioms equalsOneModel
end models
end PA194CodeOneHit
