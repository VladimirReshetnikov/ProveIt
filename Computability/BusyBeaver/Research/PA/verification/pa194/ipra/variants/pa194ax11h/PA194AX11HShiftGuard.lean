import PA194AX11HCandidateDrain

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace PA194AX11HShiftGuard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194AX11HSourceAt PA194AX11HCandidateDrain
open PA194PausedReach (append oneStep)
open PRASubAddition PRAExhaustion


open PA194ModelMPDrain

private theorem row0 : PA194AX11HSource.program[0]'(by rw [PA194AX11HSource.program_length]; decide) = some (.dec 5 (some 4) (some 1)) := by decide +kernel
private theorem row1 : PA194AX11HSource.program[1]'(by rw [PA194AX11HSource.program_length]; decide) = some (.dec 6 (some 3) (some 2)) := by decide +kernel
private theorem row2 : PA194AX11HSource.program[2]'(by rw [PA194AX11HSource.program_length]; decide) = some (.jump (some 0)) := by decide +kernel
private theorem row3 : PA194AX11HSource.program[3]'(by rw [PA194AX11HSource.program_length]; decide) = some (.jump (some 5)) := by decide +kernel
private theorem row4 : PA194AX11HSource.program[4]'(by rw [PA194AX11HSource.program_length]; decide) = some (.dec 6 (some 10) (some 5)) := by decide +kernel
private theorem row5 : PA194AX11HSource.program[5]'(by rw [PA194AX11HSource.program_length]; decide) = some (.dec 5 (some 7) (some 6)) := by decide +kernel
private theorem row6 : PA194AX11HSource.program[6]'(by rw [PA194AX11HSource.program_length]; decide) = some (.jump (some 5)) := by decide +kernel
private theorem row7 : PA194AX11HSource.program[7]'(by rw [PA194AX11HSource.program_length]; decide) = some (.dec 6 (some 9) (some 8)) := by decide +kernel
private theorem row9 : PA194AX11HSource.program[9]'(by rw [PA194AX11HSource.program_length]; decide) = some (.jump (some 11)) := by decide +kernel

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

private theorem clearFromFive (args : Fin 11 → M) (suffix : M) (hx : args 6 = 0) :
    R (sourceState 5 args suffix)
      (sourceState 11 (Function.update args 5 0) suffix) := by
  let out := Function.update args 5 (0 : M)
  have eq : argsAfter args 5 [] (args 5) = out := by
    funext i
    fin_cases i <;> simp [out,argsAfter,location,tally,subSelf,
      show modelNumeral M 0 = (0 : M) from rfl]
  have h0 := PA194AX11HCandidateDrain.drain 5 6 7 5 [] (by decide) row5 (.jump 6 (by decide) row6)
    (by decide) args suffix
  change R (sourceState 5 args suffix)
    (sourceState 7 (argsAfter args 5 [] (args 5)) suffix) at h0
  rw [eq] at h0
  have hz : regsOfArgs out 6 = (0 : M) := by simp [out,regsOfArgs,hx]
  have h1 := sourceDecZero 7 9 6 (some 8) (by decide) row7 out suffix hz
  have h2 := sourceJump 9 11 (by decide) row9 out suffix
  exact append PA194AX11HSource.step (append PA194AX11HSource.step h0 (oneStep PA194AX11HSource.step h1)) (oneStep PA194AX11HSource.step h2)

/-- For a cache other than one, the SHIFT guard clears it and reaches
the stack reader. The scratch register is clear at both boundaries. -/
theorem guardReturns (args : Fin 11 → M) (suffix : M)
    (hx : args 6 = 0) (hne : args 5 ≠ 1) :
    R (sourceState 0 (Function.update args 6 1) suffix)
      (sourceState 11 (Function.update args 5 0) suffix) := by
  let a := Function.update args 6 (1 : M)
  rcases zero_or_succ (args 5) with hz | ⟨m,hm⟩
  · have h5 : regsOfArgs a 5 = (0 : M) := by simp [a,regsOfArgs,hz]
    have h6 : regsOfArgs a 6 = (0 : M)+1 := by simp [a,regsOfArgs]
    have h0 := sourceDecZero 0 4 5 (some 1) (by decide) row0 a suffix h5
    have h4 : F PA194AX11HSource.step ![sourceState 4 a suffix] = sourceState 5 args suffix := by
      have h := sourceDecPositive 4 5 6 (some 10) (by decide) row4 a suffix 0 h6
      change F PA194AX11HSource.step ![sourceState 4 a suffix] = sourceState 5 (Function.update a 6 0) suffix at h
      have ha : Function.update a 6 (0 : M) = args := by
        rw [←hx]
        simp [a,Function.update_idem]
      simpa only [ha] using h
    exact append PA194AX11HSource.step (append PA194AX11HSource.step (oneStep PA194AX11HSource.step h0) (oneStep PA194AX11HSource.step h4))
      (clearFromFive args suffix hx)
  · rcases zero_or_succ m with hm0 | ⟨k,hk⟩
    · exact (hne (by simp only [hm,hm0,zero_add])).elim
    · let b := Function.update a 5 (k+1)
      let c := Function.update b 6 (0 : M)
      let e := Function.update c 5 k
      have hb : regsOfArgs a 5 = (k+1)+1 := by simp [a,regsOfArgs,hm,hk]
      have h0 : F PA194AX11HSource.step ![sourceState 0 a suffix] = sourceState 1 b suffix :=
        sourceDecPositive 0 1 5 (some 4) (by decide) row0 a suffix (k+1) hb
      have h6 : regsOfArgs b 6 = (0 : M)+1 := by simp [b,a,regsOfArgs]
      have h1 : F PA194AX11HSource.step ![sourceState 1 b suffix] = sourceState 2 c suffix :=
        sourceDecPositive 1 2 6 (some 3) (by decide) row1 b suffix 0 h6
      have h2 := sourceJump 2 0 (by decide) row2 c suffix
      have hc : regsOfArgs c 5 = k+1 := by simp [c,b,regsOfArgs]
      have h0' : F PA194AX11HSource.step ![sourceState 0 c suffix] = sourceState 1 e suffix :=
        sourceDecPositive 0 1 5 (some 4) (by decide) row0 c suffix k hc
      have hscratch : regsOfArgs e 6 = (0 : M) := by simp [e,c,regsOfArgs]
      have h1' := sourceDecZero 1 3 6 (some 2) (by decide) row1 e suffix hscratch
      have h3 := sourceJump 3 5 (by decide) row3 e suffix
      have endEq : Function.update e 5 (0 : M) = Function.update args 5 0 := by
        funext i
        fin_cases i <;> simp [e,c,b,a,hx]
      have hclear := clearFromFive e suffix hscratch
      rw [endEq] at hclear
      exact append PA194AX11HSource.step (append PA194AX11HSource.step
        (append PA194AX11HSource.step (append PA194AX11HSource.step (append PA194AX11HSource.step (append PA194AX11HSource.step (oneStep PA194AX11HSource.step h0)
          (oneStep PA194AX11HSource.step h1)) (oneStep PA194AX11HSource.step h2)) (oneStep PA194AX11HSource.step h0'))
          (oneStep PA194AX11HSource.step h1')) (oneStep PA194AX11HSource.step h3)) hclear

#print axioms guardReturns
end models
end PA194AX11HShiftGuard
