import PA194Site49PositivePath
import PA194SourceSite49Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194SourceSite49PositivePhysical
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

theorem positiveBranch (j tail m : M) (args : Fin 11 → M) (hm : args 3 = m+1) :
    F step ![sourceState 49 args tail] = sourceState 50 (Function.update args 3 m) tail ∧
    F PA194Stepper.stepper ![F addCode ![PA194Site49PositiveTo16.clock (((j+1)+1)+1) args,modelNumeral M 24],
      PA194Site49Branch.runTo4 (((j+1)+1)+1) args] = physicalFrame 50 j (Function.update args 3 m) := by
  exact ⟨PA194SourceSite49Controller.positiveBranch args tail m hm,PA194Site49PositivePath.positivePath j m args hm⟩
#print axioms positiveBranch
end models
end PA194SourceSite49PositivePhysical
