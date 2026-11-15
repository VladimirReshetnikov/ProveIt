import PA194IteratedSimulation
import PA194ClockInvariantDefinable
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ControllerRunAdd
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PA194IteratedSimulation PA194ClockInvariantDefinable
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

theorem runAddDef (f g : M → M) (a : M) (hf : 𝚺₁-Function₁ f) (hg : 𝚺₁-Function₁ g) :
    𝚺₁-Predicate (fun b : M => f (a+b) = g b) := by
  haveI := hf
  haveI := hg
  definability

theorem iterateAdd (next : Code 1) (a b seed : M) :
    F (iterate next) ![a+b,seed] = F (iterate next) ![b,F (iterate next) ![a,seed]] := by
  let f : M → M := fun t => F (iterate next) ![t,seed]
  let g : M → M := fun t => F (iterate next) ![t,F (iterate next) ![a,seed]]
  have hf : 𝚺₁-Function₁ f := bindBinary _ seed (binaryCodeDef (M := M) (iterate next))
  have hg : 𝚺₁-Function₁ g := bindBinary _ (F (iterate next) ![a,seed]) (binaryCodeDef (M := M) (iterate next))
  have hp := runAddDef f g a hf hg
  change f (a+b) = g b
  induction b using ISigma1.sigma1_succ_induction with
  | hP => exact hp
  | zero =>
    dsimp only [f,g]
    rw [add_zero,iterateZero]
  | succ b ih =>
    dsimp only [f,g] at ih ⊢
    rw [←add_assoc,iterateSucc,iterateSucc,ih]
#print axioms runAddDef
#print axioms iterateAdd
end models
end PA194ControllerRunAdd
