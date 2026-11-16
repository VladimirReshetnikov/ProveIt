import PA194AX11HWindowDrain
import PA194ModelMPTransfer

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

namespace PA194WindowTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194ModelMPTransfer
open PA194PausedReach PA194WindowDrain

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

/-- The ordinary three-row transfer has the same full register effect under
any code agreeing below the boundary, provided its executed rows are below it. -/
theorem transfer (code : Code 1) (lower bound base exit : Nat) (r q : Fin 9)
    (hagrees : AgreesWindow (M := M) code lower bound)
    (rows : TransferRows base exit r q) (hbase : lower ≤ base) (hbelow : base+2 < bound)
    (hne : r ≠ q) (a : Fin 11 → M) (tail : M) :
    PA194PausedReach.Reaches code (sourceState base a tail) (sourceState exit (transferArgs a r q) tail) := by
  have path : SafeIncrements lower bound base (base+1) [q] :=
    .inc _ _ _ _ (by have := rows.valid; omega) (by omega) (by omega) rows.output
      (.jump _ rows.valid (by omega) hbelow rows.repeatInput)
  have h := PA194WindowDrain.drain code lower bound hagrees base (base+1) exit r [q]
    (by have := rows.valid; omega) (by omega) (by omega) rows.input path (by simp [hne]) a tail
  rwa [transferArgs_eq a r q hne] at h

#print axioms transfer
end models
end PA194WindowTransfer
