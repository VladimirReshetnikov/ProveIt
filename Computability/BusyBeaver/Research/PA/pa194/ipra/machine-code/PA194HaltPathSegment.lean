import PA194ControllerHalt
import PA194Path27Header
import PA194GatedActiveHit
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194HaltPathSegment
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PA194Stepper PA194StepperCompose
open PA194ControllerHalt PA194Path27Header PA194GatedActiveHit PA194ActivePrefix
open TableDispatch

theorem path10 : PA194SourceProgram.path 10 = [false,false,true] := by decide +kernel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- The actual site-10 path, followed by arbitrary model-valued suffix,
    reaches terminal control after exactly three physical steps. -/
theorem haltPathSegment (l suffix : M) :
    F stepper ![modelNumeral M 3,
      F pairCode ![modelNumeral M 24,F pairCode ![l,modelWord (PA194SourceProgram.path 10) suffix]]] =
    F pairCode ![modelNumeral M 194,F pairCode ![(l+l+l+l)+(l+l+l+l)+1,suffix]] := by
  rw [path10]
  simp only [modelWord, Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false]
  exact threeSteps l suffix

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- Under a synchronized code run, every nonzero code hit leads to the
    literal halt when hit frames have the actual site-10 prefix. -/
theorem codeHitReachesLiteralHalt
    (run : Code 2) (hit : Code 1) (seed : M)
    (tape left suffix elapsed : M → M) (good : M → Prop) (start n : M)
    (hsync : ∀ i, F (active run hit) ![i,seed] = 1 →
      good (F run ![i,seed]) ∧
      F stepper ![elapsed i,start] = F pairCode ![modelNumeral M 24,tape (F run ![i,seed])] ∧
      i ≤ elapsed i)
    (htape : ∀ s, F hit ![s] ≠ 0 → tape s =
      F pairCode ![left s,modelWord (PA194SourceProgram.path 10) (suffix s)])
    (hh : F hit ![F run ![n,seed]] ≠ 0) :
    ∃ i, i ≤ n ∧
      ¬ pi₁ (F stepper ![F addCode ![elapsed i,modelNumeral M 3],start]) < modelNumeral M 194 := by
  apply codeHitToHalt run hit seed
    (fun s => F pairCode ![modelNumeral M 24,tape s])
    elapsed (fun _ => modelNumeral M 3) good
    (fun x => ¬ pi₁ x < modelNumeral M 194) start hsync _ n hh
  intro s _ hhit
  rw [htape s hhit,haltPathSegment,modelPairCode,pi₁_pair]
  exact _root_.lt_irrefl _
#print axioms path10
#print axioms haltPathSegment
#print axioms codeHitReachesLiteralHalt
end models
end PA194HaltPathSegment
