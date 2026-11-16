import PA194ModelMPDrain

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

namespace PA194ShiftModelGuardReturn
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceFetchLoop
open PA194SourceFetchRestoreLoop PA194SourceControllerStep PA194IteratedSimulation


open PA194ModelMPDrain

private theorem row3671 : row 3671 = some (.inc 6 (some 3672)) := by decide +kernel
private theorem row3672 : row 3672 = some (.jump (some 0)) := by decide +kernel
private theorem row0 : row 0 = some (.dec 5 (some 4) (some 1)) := by decide +kernel
private theorem row1 : row 1 = some (.dec 6 (some 3) (some 2)) := by decide +kernel
private theorem row2 : row 2 = some (.jump (some 0)) := by decide +kernel
private theorem row3 : row 3 = some (.jump (some 5)) := by decide +kernel
private theorem row4 : row 4 = some (.dec 6 (some 10) (some 5)) := by decide +kernel
private theorem row5 : row 5 = some (.dec 5 (some 7) (some 6)) := by decide +kernel
private theorem row6 : row 6 = some (.jump (some 5)) := by decide +kernel
private theorem row7 : row 7 = some (.dec 6 (some 9) (some 8)) := by decide +kernel
private theorem row9 : row 9 = some (.jump (some 11)) := by decide +kernel

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

private theorem clearFromFive (args : Fin 11 → M) (suffix : M) (hx : args 6 = 0) :
    ReachesPositive (sourceState 5 args suffix)
      (sourceState 11 (Function.update args 5 0) suffix) := by
  let out := Function.update args 5 (0 : M)
  have eq : argsAfter args 5 [] (args 5) = out := by
    funext i
    fin_cases i <;> simp [out,argsAfter,location,tally,subSelf,
      show modelNumeral M 0 = (0 : M) from rfl]
  have h0 := drain 5 6 7 5 [] (by decide) row5 (.jump 6 (by decide) row6)
    (by decide) args suffix
  change ReachesPositive (sourceState 5 args suffix)
    (sourceState 7 (argsAfter args 5 [] (args 5)) suffix) at h0
  rw [eq] at h0
  have hz : regsOfArgs out 6 = (0 : M) := by simp [out,regsOfArgs,hx]
  have h1 := sourceDecZero 7 9 6 (some 8) (by decide) row7 out suffix hz
  have h2 := sourceJump 9 11 (by decide) row9 out suffix
  exact appendPositive (append h0.reaches (oneStep h1).reaches) (oneStep h2)

private theorem initialSteps (args : Fin 11 → M) (suffix : M) (hx : args 6 = 0) :
    Reaches (sourceState 3671 args suffix)
      (sourceState 0 (Function.update args 6 1) suffix) := by
  let a := Function.update args 6 (1 : M)
  have h : args 6+1 = (1 : M) := by simp [hx]
  have h1 : F step ![sourceState 3671 args suffix] = sourceState 3672 a suffix := by
    have hstep := sourceInc 3671 3672 6 (by decide) row3671 args suffix
    change F step ![sourceState 3671 args suffix] =
      sourceState 3672 (Function.update args 6 (args 6+1)) suffix at hstep
    rwa [h] at hstep
  exact append (oneStep h1).reaches (oneStep (sourceJump 3672 0 (by decide) row3672 a suffix)).reaches

/-- For a cache other than one, the SHIFT guard clears it and reaches
the stack reader. The scratch register is clear at both boundaries. -/
theorem guardReturns (args : Fin 11 → M) (suffix : M)
    (hx : args 6 = 0) (hne : args 5 ≠ 1) :
    ReachesPositive (sourceState 3671 args suffix)
      (sourceState 11 (Function.update args 5 0) suffix) := by
  let a := Function.update args 6 (1 : M)
  have hinit := initialSteps args suffix hx
  change Reaches (sourceState 3671 args suffix) (sourceState 0 a suffix) at hinit
  rcases zero_or_succ (args 5) with hz | ⟨m,hm⟩
  · have h5 : regsOfArgs a 5 = (0 : M) := by simp [a,regsOfArgs,hz]
    have h6 : regsOfArgs a 6 = (0 : M)+1 := by simp [a,regsOfArgs]
    have h0 := sourceDecZero 0 4 5 (some 1) (by decide) row0 a suffix h5
    have h4 : F step ![sourceState 4 a suffix] = sourceState 5 args suffix := by
      have h := sourceDecPositive 4 5 6 (some 10) (by decide) row4 a suffix 0 h6
      change F step ![sourceState 4 a suffix] = sourceState 5 (Function.update a 6 0) suffix at h
      have ha : Function.update a 6 (0 : M) = args := by
        rw [←hx]
        simp [a,Function.update_idem]
      simpa only [ha] using h
    exact appendPositive (append (append hinit (oneStep h0).reaches) (oneStep h4).reaches)
      (clearFromFive args suffix hx)
  · rcases zero_or_succ m with hm0 | ⟨k,hk⟩
    · exact (hne (by simp only [hm,hm0,zero_add])).elim
    · let b := Function.update a 5 (k+1)
      let c := Function.update b 6 (0 : M)
      let e := Function.update c 5 k
      have hb : regsOfArgs a 5 = (k+1)+1 := by simp [a,regsOfArgs,hm,hk]
      have h0 : F step ![sourceState 0 a suffix] = sourceState 1 b suffix :=
        sourceDecPositive 0 1 5 (some 4) (by decide) row0 a suffix (k+1) hb
      have h6 : regsOfArgs b 6 = (0 : M)+1 := by simp [b,a,regsOfArgs]
      have h1 : F step ![sourceState 1 b suffix] = sourceState 2 c suffix :=
        sourceDecPositive 1 2 6 (some 3) (by decide) row1 b suffix 0 h6
      have h2 := sourceJump 2 0 (by decide) row2 c suffix
      have hc : regsOfArgs c 5 = k+1 := by simp [c,b,regsOfArgs]
      have h0' : F step ![sourceState 0 c suffix] = sourceState 1 e suffix :=
        sourceDecPositive 0 1 5 (some 4) (by decide) row0 c suffix k hc
      have hscratch : regsOfArgs e 6 = (0 : M) := by simp [e,c,regsOfArgs]
      have h1' := sourceDecZero 1 3 6 (some 2) (by decide) row1 e suffix hscratch
      have h3 := sourceJump 3 5 (by decide) row3 e suffix
      have endEq : Function.update e 5 (0 : M) = Function.update args 5 0 := by
        funext i
        fin_cases i <;> simp [e,c,b,a,hx]
      have hclear := clearFromFive e suffix hscratch
      rw [endEq] at hclear
      exact appendPositive (append
        (append (append (append (append (append hinit (oneStep h0).reaches)
          (oneStep h1).reaches) (oneStep h2).reaches) (oneStep h0').reaches)
          (oneStep h1').reaches) (oneStep h3).reaches) hclear

#print axioms guardReturns
end models
end PA194ShiftModelGuardReturn
