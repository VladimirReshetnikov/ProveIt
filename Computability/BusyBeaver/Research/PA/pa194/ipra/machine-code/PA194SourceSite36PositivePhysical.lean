import PA194Site36PositivePath
import PA194SourceSite36Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194SourceSite36PositivePhysical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SourceControllerCode PA194SourceSite31Controller PA194SourceSite31Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem positiveBranch (k tail m : M) (args : Fin 11 → M) (hm : args 6 = m+1) :
    F step ![sourceState 36 args tail] = sourceState 37 (Function.update args 6 m) tail ∧
    F PA194Stepper.stepper ![F addCode ![PA194Site36PositiveTo16.clock k args,modelNumeral M 27],
      PA194Site36Branch.runTo4 k args] = physicalFrame 37 (((k+1)+1)+1) (Function.update args 6 m) := by
  exact ⟨PA194SourceSite36Controller.positiveBranch args tail m hm,PA194Site36PositivePath.positivePath k m args hm⟩
#print axioms positiveBranch
end models
end PA194SourceSite36PositivePhysical
