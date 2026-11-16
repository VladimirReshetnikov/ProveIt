import PA194AX11HCopyAlgebra
import PA194AX11HCopyPaths
set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2000000
namespace PA194AX11HCopyFirst
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194AX11HCompareRows PA194AX11HCopyPaths
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem copyFirst (a : Fin 11 → M) (tail : M) (hX : a 6 = 0) :
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 3652 a tail)
      (sourceState 3656 (PA194AX11HCopyAlgebra.mid a) tail) := by
  have h := PA194AX11HCandidateDrain.drain 3652 3653 3656 4 [1,6] (by decide)
    s3652 path1 (by decide) a tail
  rwa [PA194AX11HCopyAlgebra.mid_eq a hX] at h

#print axioms copyFirst
end models
end PA194AX11HCopyFirst
