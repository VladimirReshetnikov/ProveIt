import PA194ADFrame
import PA194StartupSourceFrame
set_option autoImplicit false
namespace PA194ADSeed
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194UnaryRuns PA194ZeroRuns
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩

theorem seedFrame_eq (q : Nat) (gap : M) :
    PA194ADFrame.frame q gap (fun i => modelNumeral M (PA194StartupSourceFrame.seedArgs i)) =
    PA194SourceSite31Physical.physicalFrame q gap (fun i => modelNumeral M (PA194StartupSourceFrame.seedArgs i)) := by
  apply PA194ADFrame.sameFrame_of_equal_AD
  rfl

theorem seedRight_companionLayout :
    let f := F PA194ADFile.sourceFileCode (fun i => modelNumeral M (PA194StartupSourceFrame.seedArgs i))
    let x := F zeros ![modelNumeral M 47,f+f+1]
    modelNumeral M (PA194Bounded.bits PA194StartupData.seedFrame.r) = x+x+1 := by
  dsimp only
  rw [PA194ADFile.modelSourceFile_swap,
    PA194ADFrame.swapLogical_eq_self _ (by rfl)]
  exact PA194StartupSourceFrame.seedRight_sourceLayout

#print axioms seedFrame_eq
#print axioms seedRight_companionLayout
end models
end PA194ADSeed
