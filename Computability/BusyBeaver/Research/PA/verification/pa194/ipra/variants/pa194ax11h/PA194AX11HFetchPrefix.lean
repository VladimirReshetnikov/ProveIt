import PA194AX11HFetchRestore
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194AX11HFetchPrefix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation
open PA194SourceFetchLoop PA194SourceFetchRestoreLoop PA194ModelMPDrain PA194PausedReach PA194PausedDrain

theorem row25 : row 25 = some (.dec 8 (some 27) (some 26)) := by decide +kernel

theorem drainPath : SafeIncrements 48 27 28 [8,6] :=
  .inc 28 29 8 [6] (by decide) (by decide) inst28
    (.inc 29 30 6 [] (by decide) (by decide) inst29
      (.jump 30 (by decide) (by decide) inst30))

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

theorem fresh (a : Fin 11 → M) (tail : M) (h : a 8 = 0) :
    let b := argsAfter a 0 [8,6] (a 0)
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 25 a tail)
      (sourceState 34 (Function.update (Function.update b 0 (b 0 + b 6 + 1)) 6 0) tail) := by
  dsimp only
  let b := argsAfter a 0 [8,6] (a 0)
  have s25 := sourceDecZero 25 27 8 (some 26) (by decide) row25 a tail h
  have e25 : F PA194AX11HSource.step ![sourceState 25 a tail] = sourceState 27 a tail := by
    rw [PA194AX11HFetchAgree.agrees 25 (by decide) a tail]
    exact s25
  have hd := PA194PausedDrain.drain PA194AX11HSource.step 48 PA194AX11HFetchAgree.agrees
    27 28 31 0 [8,6] (by decide) (by decide) inst27 drainPath (by decide) a tail
  change PA194PausedReach.Reaches _ (sourceState 27 a tail) (sourceState 31 b tail) at hd
  exact PA194PausedReach.append _ (PA194PausedReach.oneStep _ e25)
    (PA194PausedReach.append _ hd (PA194AX11HFetchRestore.restore b tail))

theorem positive (a : Fin 11 → M) (tail m : M) (h : a 8 = m+1) :
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 25 a tail)
      (sourceState 34 (Function.update a 8 m) tail) := by
  let b := Function.update a 8 m
  have e25 : F PA194AX11HSource.step ![sourceState 25 a tail] = sourceState 26 b tail := by
    rw [PA194AX11HFetchAgree.agrees 25 (by decide) a tail]
    exact sourcePositive25 a tail m h
  have e26 : F PA194AX11HSource.step ![sourceState 26 b tail] = sourceState 34 b tail := by
    rw [PA194AX11HFetchAgree.agrees 26 (by decide) b tail]
    exact sourceJump26 b tail
  exact PA194PausedReach.append _ (PA194PausedReach.oneStep _ e25) (PA194PausedReach.oneStep _ e26)
#print axioms fresh
#print axioms positive
end models
end PA194AX11HFetchPrefix
