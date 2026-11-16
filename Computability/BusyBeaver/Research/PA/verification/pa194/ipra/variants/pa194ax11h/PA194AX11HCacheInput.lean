import PA194AX11HCandidateDrain
import PA194AX11HMPDispatch

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace PA194AX11HCacheInput
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PRASubAddition
open PA194SchedulerFetchPositive PA194AX11HCandidateDrain PA194AX11HSourceAt PA194ModelMPDrain

private theorem clearTop : CandidateIncrements 3660 3661 [] :=
  .jump 3661 (by decide) (by decide +kernel)

private theorem copyCache : CandidateIncrements 3662 3663 [1,6] :=
  .inc 3663 3664 1 [6] (by decide) (by decide +kernel)
    (.inc 3664 3665 6 [] (by decide) (by decide +kernel)
      (.jump 3665 (by decide) (by decide +kernel)))

private theorem restoreCache : CandidateIncrements 3666 3667 [5] :=
  .inc 3667 3668 5 [] (by decide) (by decide +kernel)
    (.jump 3668 (by decide) (by decide +kernel))

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

local notation "R" => PA194PausedReach.Reaches PA194AX11HSource.step
open PA194PausedReach (append oneStep)

noncomputable def testInput (a : Fin 11 → M) : Fin 11 → M :=
  Function.update (Function.update a 1 (a 5)) 6 1

theorem prepare (a : Fin 11 → M) (tail : M) (opcode : a 3 = 0) (scratch : a 6 = 0) :
    R (sourceState 48 a tail) (sourceState 0 (testInput a) tail) := by
  let cleared := Function.update a 1 (0 : M)
  let copied := Function.update (Function.update (Function.update a 1 (a 5)) 5 (0 : M)) 6 (a 5)
  let restored := Function.update (Function.update a 1 (a 5)) 6 (0 : M)
  have mn0 : modelNumeral M 0 = (0 : M) := rfl
  have ec : argsAfter a 1 [] (a (location 1)) = cleared := by
    funext i
    fin_cases i <;> simp [cleared,argsAfter,location,tally,subSelf,mn0]
  have ep : argsAfter cleared 5 [1,6] (cleared (location 5)) = copied := by
    funext i
    fin_cases i <;> simp [cleared,copied,argsAfter,location,tally,subSelf,mn0,
      PA194StateOne.modelNumeralOne,scratch]
  have er : argsAfter copied 6 [5] (copied (location 6)) = restored := by
    funext i
    fin_cases i <;> simp [copied,restored,argsAfter,location,tally,subSelf,mn0,
      PA194StateOne.modelNumeralOne]
  have h48 := sourceDecZero 48 3660 3 (some 49) (by decide) PA194AX11HMPDispatch.row48 a tail
    (by simpa [regsOfArgs] using opcode)
  have h0 := PA194AX11HCandidateDrain.drain 3660 3661 3662 1 [] (by decide) (by decide +kernel)
    clearTop (by decide) a tail
  rw [ec] at h0
  have h1 := PA194AX11HCandidateDrain.drain 3662 3663 3666 5 [1,6] (by decide) (by decide +kernel)
    copyCache (by decide) cleared tail
  rw [ep] at h1
  have h2 := PA194AX11HCandidateDrain.drain 3666 3667 3669 6 [5] (by decide) (by decide +kernel)
    restoreCache (by decide) copied tail
  rw [er] at h2
  have h3 : F PA194AX11HSource.step ![sourceState 3669 restored tail] =
      sourceState 3670 (testInput a) tail := by
    simpa [regsOfArgs,restored,testInput,Function.update_idem] using
      sourceInc 3669 3670 6 (by decide) (by decide +kernel) restored tail
  have h4 := sourceJump 3670 0 (by decide) (by decide +kernel) (testInput a) tail
  have finish := append PA194AX11HSource.step (oneStep PA194AX11HSource.step h3)
    (oneStep PA194AX11HSource.step h4)
  have copiedAndRestored := append PA194AX11HSource.step h1 h2
  have dispatched := append PA194AX11HSource.step (oneStep PA194AX11HSource.step h48) h0
  exact append PA194AX11HSource.step (append PA194AX11HSource.step dispatched copiedAndRestored) finish

#print axioms prepare
end models
end PA194AX11HCacheInput
