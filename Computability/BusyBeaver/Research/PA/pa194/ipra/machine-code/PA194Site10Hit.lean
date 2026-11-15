import PA194HaltPathSegment
import DiophantineConsistency.PRAEqualityCode
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site10Hit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PA194Stepper PA194StepperCompose
open PA194ControllerHalt PA194Path27Header PA194GatedActiveHit PA194ActivePrefix
open TableDispatch PRAEqualityCode PRABooleanOps PA194CumulativeClock PA194HaltPathSegment

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen


/-- A finite characteristic code for the controller program counter at site 10. -/
def atSite10 (pc : Code 1) : Code 1 := bin equalityCode pc (constantCode 10)

theorem atSite10Model (pc : Code 1) (x : M) :
    F (atSite10 pc) ![x] ≠ 0 ↔ F pc ![x] = modelNumeral M 10 := by
  rw [atSite10,modelBin]
  have hconstant : F (constantCode 10) ![x] = modelNumeral M 10 := by
    have hv : (![x] : Fin 1 → M) = fun _ => x := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [hv,modelConstant]
  rw [hconstant]
  have ⟨hb,hc⟩ := modelEqualityCode (F pc ![x]) (modelNumeral M 10)
  constructor
  · intro hn
    have he : F equalityCode ![F pc ![x],modelNumeral M 10] = 1 := hb.resolve_left hn
    exact hc.mp he
  · intro he hz
    have ho := hc.mpr he
    rw [hz] at ho
    exact (ne_of_lt (Arithmetic.zero_lt_one : (0 : M) < 1)) ho

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- Bounded literal halt from the concrete site-10 characteristic, conditional
    on synchronization and the program-counter/frame representation. -/
theorem site10ReachesLiteralHalt
    (run : Code 2) (pc : Code 1) (seed : M)
    (tape left suffix elapsed : M → M) (good : M → Prop) (start n : M)
    (hsync : ∀ i, F (active run (atSite10 pc)) ![i,seed] = 1 →
      good (F run ![i,seed]) ∧
      F stepper ![elapsed i,start] = F pairCode ![modelNumeral M 24,tape (F run ![i,seed])] ∧
      i ≤ elapsed i)
    (htape : ∀ s, F pc ![s] = modelNumeral M 10 → tape s =
      F pairCode ![left s,modelWord (PA194SourceProgram.path 10) (suffix s)])
    (hh : F pc ![F run ![n,seed]] = modelNumeral M 10) :
    ∃ i, i ≤ n ∧
      ¬ pi₁ (F stepper ![F addCode ![elapsed i,modelNumeral M 3],start]) < modelNumeral M 194 := by
  apply codeHitReachesLiteralHalt run (atSite10 pc) seed tape left suffix elapsed good start n hsync _
    ((atSite10Model pc _).mpr hh)
  intro s h
  exact htape s ((atSite10Model pc s).mp h)
#print axioms atSite10Model
#print axioms site10ReachesLiteralHalt
end models
end PA194Site10Hit
