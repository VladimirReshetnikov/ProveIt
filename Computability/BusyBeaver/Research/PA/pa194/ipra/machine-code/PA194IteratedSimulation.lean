import PA194ClockedSimulation
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194IteratedSimulation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PA194CumulativeClock PA194Stepper
open PA194ClockedSimulation

/-- Primitive recursion of an arbitrary unary modeled transition. The code has
    exactly the same syntactic shape as `PA194StackCode.dropCode next`. -/
def iterate (next : Code 1) : Code 2 := .prec (.proj 0) (unary next (.proj 1))
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

theorem iterateZero (next : Code 1) (seed : M) : F (iterate next) ![0,seed] = seed := by
  have h := modelBase (M := M) (.proj 0) (unary next (.proj 1)) ![seed]
  change F (iterate next) ![0,seed] = F (.proj 0) ![seed] at h
  rw [modelProjection] at h
  exact h

theorem iterateSucc (next : Code 1) (n seed : M) :
    F (iterate next) ![n+1,seed] = F next ![F (iterate next) ![n,seed]] := by
  have h := modelStep (M := M) (.proj 0) (unary next (.proj 1)) ![n,seed]
  change F (iterate next) ![F Code.succ (fun _ => n),seed] =
    F (unary next (.proj 1)) ![n,F (iterate next) ![n,seed],seed] at h
  rw [←modelAddOne] at h
  change F (iterate next) ![n+1,seed] = _ at h
  rw [h,modelUnary,modelProjection]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem simulateIterated (next cost frame : Code 1) (seed start : M)
    (good : M → Prop) (hgood : 𝚺₁-Predicate good)
    (hinit : good seed) (hframe : start = F frame ![seed])
    (hpres : ∀ s : M, good s → good (F next ![s]))
    (hsegment : ∀ s : M, good s →
      F stepper ![F cost ![s],F frame ![s]] = F frame ![F next ![s]]) :
    ∀ n : M, good (F (iterate next) ![n,seed]) ∧
      F stepper ![F (clock (iterate next) cost) ![n,seed],start] =
        F frame ![F (iterate next) ![n,seed]] := by
  apply simulateCodeRun (iterate next) next cost frame seed start good hgood
  · rw [iterateZero]
    exact hinit
  · rw [iterateZero]
    exact hframe
  · exact fun n => iterateSucc (M := M) next n seed
  · exact hpres
  · exact hsegment
#print axioms iterateZero
#print axioms iterateSucc
#print axioms simulateIterated
end models
end PA194IteratedSimulation
