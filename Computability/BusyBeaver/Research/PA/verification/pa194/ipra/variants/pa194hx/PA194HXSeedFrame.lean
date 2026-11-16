import PA194HXFrame
import PA194HXModelStartup
import PA194CompressedStartup
import PA194ModelDenseStartup
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194HXSeedFrame
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing TableDispatch PackedRootModel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem numeralCast (n : Nat) : modelNumeral M n = (n : M) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [PA194FiniteControls.modelNumeralSucc,ih,Nat.cast_succ]

/-- HX reaches its own source-root frame at the fixed standard clock. -/
theorem reachesFrame :
    ConPA.Machine.run (V := M) PA194HXDispatch.table (56134 : M) =
      PA194HXFrame.frame 25 (modelNumeral M 42) (PA194CompressedStartup.startArgs (M := M)) := by
  have hp := PA194ModelDenseStartup.modelDenseStartup (M := M)
  have hr := PA194CompressedStartup.blankToRoot (M := M)
  rw [show modelNumeral M 0 = (0 : M) from rfl] at hp
  have he : PA194CompressedStartup.startArgs (M := M) 5 = PA194CompressedStartup.startArgs 6 := by rfl
  rw [PA194HXFrame.sameFrame_of_equal_HX _ _ _ he]
  rw [← hr, PA194HXModelStartup.modeledStartup]
  rw [hp]
  simp only [numeralCast, modelPairCode, Nat.cast_ofNat, Nat.cast_one]

#print axioms reachesFrame
end models
end PA194HXSeedFrame
