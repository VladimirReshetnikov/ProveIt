import PA194ResolvedComplete
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ResolvedModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourceNoMalformed
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

/-- The checked pinned source tree never reaches malformed control when
    started in a valid source or halted state, at any model-valued time. -/
theorem runValidPC (seed : M)
    (hseed : F pc ![seed] < modelNumeral M 3673 ∨ F pc ![seed] = modelNumeral M 3674) :
    ∀ n : M, F pc ![F run ![n,seed]] < modelNumeral M 3673 ∨
      F pc ![F run ![n,seed]] = modelNumeral M 3674 :=
  PA194SourceNoMalformed.runValidPC PA194ResolvedComplete.allResolved seed hseed
#print axioms runValidPC
end models
end PA194ResolvedModel
