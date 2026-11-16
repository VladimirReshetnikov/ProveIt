import PA194ProgramDrain
import PA194ModelMPTransfer

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1300000
set_option linter.unusedSectionVars false

namespace PA194ProgramTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194ProgramDrain
open PA194ModelMPTransfer (transferArgs transferArgs_eq)

structure TransferRows (program : Program) (base exit : Nat) (r q : Fin 9) : Prop where
  valid : base+2 < program.length
  input : row program base = some (.dec r (some exit) (some (base+1)))
  output : row program (base+1) = some (.inc q (some (base+2)))
  repeatInput : row program (base+2) = some (.jump (some base))

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
variable (program : Program)

theorem transfer (base exit : Nat) (r q : Fin 9) (rows : TransferRows program base exit r q)
    (hne : r ≠ q) (a : Fin 11 → M) (tail : M) :
    ReachesPositive program (sourceState base a tail) (sourceState exit (transferArgs a r q) tail) := by
  have path : Increments program base (base+1) [q] :=
    .inc _ _ _ _ (by have := rows.valid; omega) rows.output
      (.jump _ rows.valid rows.repeatInput)
  have h := PA194ProgramDrain.drain program base (base+1) exit r [q] (by have := rows.valid; omega) rows.input path
    (by simp [hne]) a tail
  rwa [transferArgs_eq a r q hne] at h

#print axioms transfer
end models
end PA194ProgramTransfer
