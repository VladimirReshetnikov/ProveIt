import PA194StepperCompose
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194CumulativeClock
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing

/-- Compose a unary function code with an n-argument code. -/
def unary {n : Nat} (f : Code 1) (x : Code n) : Code n := .comp f (.cons x (.nil n))
/-- Step arguments are `[iteration, elapsed, seed]`. -/
def clockStep (run : Code 2) (cost : Code 1) : Code 3 :=
  bin addCode (.proj 1) (unary cost (bin run (.proj 0) (.proj 2)))
/-- Sum the state-dependent cost along the coded run, starting at zero. -/
def clock (run : Code 2) (cost : Code 1) : Code 2 := .prec (.zero 1) (clockStep run cost)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩

theorem modelUnary {n : Nat} (f : Code 1) (x : Code n) (e : Fin n → M) :
    F (unary f x) e = F f (fun _ => F x e) := by
  rw [unary,modelComposition]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem clockZero (run : Code 2) (cost : Code 1) (seed : M) :
    F (clock run cost) ![0,seed] = (0 : M) := by
  have h := modelBase (M := M) (.zero 1) (clockStep run cost) ![seed]
  change F (clock run cost) ![0,seed] = F (.zero 1) ![seed] at h
  rw [PRAMultiplication.modelZero] at h
  exact h

theorem clockSucc (run : Code 2) (cost : Code 1) (n seed : M) :
    F (clock run cost) ![n+1,seed] =
      F addCode ![F (clock run cost) ![n,seed], F cost (fun _ => F run ![n,seed])] := by
  have h := modelStep (M := M) (.zero 1) (clockStep run cost) ![n,seed]
  change F (clock run cost) ![F Code.succ (fun _ => n),seed] =
    F (clockStep run cost) ![n,F (clock run cost) ![n,seed],seed] at h
  rw [←modelAddOne] at h
  change F (clock run cost) ![n+1,seed] = _ at h
  rw [h,clockStep,modelBin,modelUnary,modelBin]
  simp only [modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one]
  rfl
#print axioms clockZero
#print axioms clockSucc
end models
end PA194CumulativeClock
