import PA194Site48PositivePath
import PA194SourceSite48Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194SourceSite48PositivePhysical
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

theorem positiveBranch (k tail m : M) (args : Fin 11 → M) (hm : args 3 = m+1) :
    F step ![sourceState 48 args tail] = sourceState 49 (Function.update args 3 m) tail ∧
    F PA194Stepper.stepper ![F addCode ![PA194Site48PositiveTo16.clock k args,modelNumeral M 21],
      PA194Site48Branch.runTo4 k args] = physicalFrame 49 k (Function.update args 3 m) := by
  exact ⟨PA194SourceSite48Controller.positiveBranch args tail m hm,PA194Site48PositivePath.positivePath k m args hm⟩
#print axioms positiveBranch
end models
end PA194SourceSite48PositivePhysical
