import PA194AX11HCacheInput

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194AX11HHaltCommand
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PRASubAddition
open PA194SchedulerFetchPositive PA194AX11HCandidateDrain PA194AX11HSourceAt PA194ModelMPDrain

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

private theorem enterHalt (a : Fin 11 → M) (tail : M) (cache : a 5 = 1) (scratch : a 6 = 1) :
    ∃ b : Fin 11 → M, R (sourceState 0 a tail) (sourceState 10 b tail) := by
  let x := Function.update a 5 0
  let y := Function.update x 6 0
  have h0 := sourceDecPositive 0 1 5 (some 4) (by decide) (by decide +kernel) a tail 0
    (by simpa [regsOfArgs] using cache)
  have h1 := sourceDecPositive 1 2 6 (some 3) (by decide) (by decide +kernel) x tail 0
    (by simpa [regsOfArgs,x] using scratch)
  have h2 := sourceJump 2 0 (by decide) (by decide +kernel) y tail
  have h3 := sourceDecZero 0 4 5 (some 1) (by decide) (by decide +kernel) y tail
    (by simp [regsOfArgs,y,x])
  have h4 := sourceDecZero 4 10 6 (some 5) (by decide) (by decide +kernel) y tail
    (by simp [regsOfArgs,y])
  refine ⟨y, ?_⟩
  exact append PA194AX11HSource.step (oneStep PA194AX11HSource.step h0) (append PA194AX11HSource.step (oneStep PA194AX11HSource.step h1)
    (append PA194AX11HSource.step (oneStep PA194AX11HSource.step h2) (append PA194AX11HSource.step (oneStep PA194AX11HSource.step h3) (oneStep PA194AX11HSource.step h4))))

/-- Opcode zero reaches the halt site when the old cache is one. -/
theorem decoded (a : Fin 11 → M) (tail : M) (opcode : a 3 = 0) (cache : a 5 = 1) (scratch : a 6 = 0) :
    ∃ b : Fin 11 → M, R (sourceState 48 a tail) (sourceState 10 b tail) := by
  let marked := PA194AX11HCacheInput.testInput a
  have start := PA194AX11HCacheInput.prepare a tail opcode scratch
  obtain ⟨b, finish⟩ := enterHalt marked tail
    (by simpa [marked,PA194AX11HCacheInput.testInput] using cache)
    (by simp [marked,PA194AX11HCacheInput.testInput])
  exact ⟨b, append PA194AX11HSource.step start finish⟩

#print axioms decoded
end models
end PA194AX11HHaltCommand
