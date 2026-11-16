import PA194CumulativeClock
import DiophantineConsistency.PRANonzeroCharacter
import ConfigurationStep
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ActivePrefix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRASelectCode PRAModelIOpenPairing PA194CumulativeClock ConfigurationStep PRANonzeroCharacter

/-- The recursion step reads `[iteration, prior flag, seed]`. Any nonzero
    hit test clears the flag; a zero test preserves it. -/
def activeStep (run : Code 2) (hit : Code 1) : Code 3 :=
  selectAmong (unary hit (bin run (.proj 0) (.proj 2))) (.zero 3) (.proj 1)
def active (run : Code 2) (hit : Code 1) : Code 2 :=
  .prec (.comp oneCode (.nil 1)) (activeStep run hit)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem activeZero (run : Code 2) (hit : Code 1) (seed : M) :
    F (active run hit) ![0,seed] = (1 : M) := by
  have h := modelBase (M := M) (.comp oneCode (.nil 1)) (activeStep run hit) ![seed]
  change F (active run hit) ![0,seed] = F (.comp oneCode (.nil 1)) ![seed] at h
  rw [modelComposition] at h
  have hv : (fun i : Fin 0 => F (getCode (.nil 1) i) ![seed]) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hv] at h
  exact h

theorem activeSucc (run : Code 2) (hit : Code 1) (n seed : M) :
    F (active run hit) ![n+1,seed] =
      F selectCode ![F hit (fun _ => F run ![n,seed]),(0 : M),F (active run hit) ![n,seed]] := by
  have h := modelStep (M := M) (.comp oneCode (.nil 1)) (activeStep run hit) ![n,seed]
  change F (active run hit) ![F Code.succ (fun _ => n),seed] =
    F (activeStep run hit) ![n,F (active run hit) ![n,seed],seed] at h
  rw [←modelAddOne] at h
  change F (active run hit) ![n+1,seed] = _ at h
  rw [h,activeStep,modelSelectAmong,modelUnary,modelBin]
  simp only [modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one,PRAMultiplication.modelZero]
  rfl

theorem activeContinues (run : Code 2) (hit : Code 1) (n seed : M)
    (ha : F (active run hit) ![n+1,seed] = (1 : M)) :
    F (active run hit) ![n,seed] = (1 : M) ∧
      F hit (fun _ => F run ![n,seed]) = (0 : M) := by
  classical
  rw [activeSucc,modelSelectAll] at ha
  by_cases hz : F hit (fun _ => F run ![n,seed]) = F (Code.zero 0) Fin.elim0
  · simp only [hz,if_true] at ha
    exact ⟨ha,hz⟩
  · simp only [hz,if_false] at ha
    have hone : F oneCode Fin.elim0 ≠ F (Code.zero 0) Fin.elim0 := modelOneNeZero (M := M)
    exact False.elim (hone ha.symm)
#print axioms activeZero
#print axioms activeSucc
#print axioms activeContinues
end models
end PA194ActivePrefix
