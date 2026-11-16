import PA194ModelMPTransfer

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

namespace PA194ShiftModelPreGuard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceFetchLoop
open PA194SourceFetchRestoreLoop PA194SourceControllerStep PA194IteratedSimulation


open PA194ModelMPDrain PA194ModelMPTransfer

private theorem moveTopRows : TransferRows 3661 3664 1 6 := by
  constructor <;> decide +kernel

private theorem moveSumRows : TransferRows 3668 3671 6 5 := by
  constructor <;> decide +kernel

private theorem moveCacheEntry : row 3664 = some (.dec 5 (some 3668) (some 3665)) := by
  decide +kernel

private theorem moveCacheRows : Increments 3664 3665 [1,6] :=
  .inc 3665 3666 1 [6] (by decide) (by decide +kernel)
    (.inc 3666 3667 6 [] (by decide) (by decide +kernel)
      (.jump 3667 (by decide) (by decide +kernel)))

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

/-- Assign the top, cache, and scratch registers in a SHIFT frame. -/
def store (args : Fin 11 → M) (top cache scratch : M) : Fin 11 → M :=
  Function.update (Function.update (Function.update args 1 top) 5 cache) 6 scratch

/-- SHIFT keeps the old cache as the next top and computes the guard sum
in the cache register, with model-valued inputs. -/
theorem runToGuard (args : Fin 11 → M) (suffix : M) (hx : args 6 = 0) :
    ReachesPositive (sourceState 3661 args suffix)
      (sourceState 3671 (store args (args 5) (args 1 + args 5) 0) suffix) := by
  let a := transferArgs args 1 6
  let b := argsAfter a 5 [1,6] (a 5)
  let c := transferArgs b 6 5
  have h1 := transfer 3661 3664 1 6 moveTopRows (by decide) args suffix
  have h2 := drain 3664 3665 3668 5 [1,6] (by decide) moveCacheEntry moveCacheRows
    (by decide) a suffix
  have h3 := transfer 3668 3671 6 5 moveSumRows (by decide) b suffix
  have heq : c = store args (args 5) (args 1 + args 5) 0 := by
    funext i
    fin_cases i <;>
      simp [a,b,c,store,transferArgs,argsAfter,tally,location,subSelf,hx,
        PA194StateOne.modelNumeralOne, show modelNumeral M 0 = (0:M) from rfl]
  rw [←heq]
  exact appendPositive (append h1.reaches h2.reaches) h3

#print axioms runToGuard
end models
end PA194ShiftModelPreGuard
