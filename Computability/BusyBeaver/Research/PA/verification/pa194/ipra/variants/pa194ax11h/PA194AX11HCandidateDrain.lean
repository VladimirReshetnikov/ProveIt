import PA194PausedReach
import PA194AX11HSourceAt

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace PA194AX11HCandidateDrain
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation PA194SourceFetchLoop
open PA194SourceFetchRestoreLoop PA194IteratedSimulation PA194ClockInvariantDefinable
open PA194PausedReach PA194ModelMPDrain

/-- A finite candidate-source increment-and-jump path. -/
inductive CandidateIncrements (exit : Nat) : Nat → List (Fin 9) → Prop where
  | jump (site : Nat) (valid : site < 3671)
      (cert : PA194AX11HSource.program[site]'(by simpa [PA194AX11HSource.program_length] using valid) = some (.jump (some exit))) :
      CandidateIncrements exit site []
  | inc (site next : Nat) (r : Fin 9) (registers : List (Fin 9)) (valid : site < 3671)
      (cert : PA194AX11HSource.program[site]'(by simpa [PA194AX11HSource.program_length] using valid) = some (.inc r (some next)))
      (rest : CandidateIncrements exit next registers) :
      CandidateIncrements exit site (r :: registers)

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


theorem incrementsRun {q exit : Nat} {rs : List (Fin 9)} (trace : CandidateIncrements exit q rs)
    (args : Fin 11 → M) (tail : M) :
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState q args tail) (sourceState exit (tick rs args) tail) := by
  induction trace generalizing args with
  | jump site valid cert =>
    have ht : tick [] args = args := by funext i; simp [tick,tally,show modelNumeral M 0 = (0:M) from rfl]
    rw [ht]
    apply PA194PausedReach.oneStep
    exact PA194AX11HSourceAt.sourceJump site _ valid cert args tail
  | inc site next r regs valid cert rest ih =>
    let out := Function.update args (location r) (args (location r)+1)
    have h := PA194AX11HSourceAt.sourceInc site next r valid cert args tail
    change F PA194AX11HSource.step ![sourceState site args tail] = sourceState next out tail at h
    apply PA194PausedReach.append PA194AX11HSource.step (t := sourceState next out tail)
    · apply PA194PausedReach.oneStep
      exact h
    · rw [←tickCons r regs args]
      exact ih out

/-- A whole model-length source-register drain for the revised AX11H code. -/
theorem drain (site first exit : Nat) (r : Fin 9) (rs : List (Fin 9))
    (valid : site < 3671)
    (entry : PA194AX11HSource.program[site]'(by simpa [PA194AX11HSource.program_length] using valid) = some (.dec r (some exit) (some first)))
    (loop : CandidateIncrements site first rs) (hr : r ∉ rs)
    (args : Fin 11 → M) (tail : M) :
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState site args tail)
      (sourceState exit (argsAfter args r rs (args (location r))) tail) := by
  let n := args (location r)
  let a := argsAfter args r rs
  let frame := fun j => sourceState site (a j) tail
  have hf : 𝚺₁-Function₁ frame := frameDef site (fun i j => a j i) tail (partialDef args r rs)
  have stepLoop (j : M) (hj : j < n) : PA194PausedReach.Reaches PA194AX11HSource.step (frame j) (frame (j+1)) := by
    obtain ⟨v,hv⟩ := le_iff_exists_add.mp (lt_iff_succ_le.mp hj)
    have hbefore : a j (location r) = v+1 := by
      simp only [a,argsAfter,if_true]
      change F subCode ![n,j] = v+1
      rw [hv,show (j+1)+v = j+(v+1) by ac_rfl]
      exact modelSubAdd j (v+1)
    let out := Function.update (a j) (location r) v
    have hs := PA194AX11HSourceAt.sourceDecPositive site first r (some exit) valid entry (a j) tail v hbefore
    change F PA194AX11HSource.step ![frame j] = sourceState first out tail at hs
    have ht : tick rs out = a (j+1) := by
      funext i
      by_cases hi : i = location r
      · subst i
        simp only [tick,out,Function.update_self,tallyZero hr,
          show modelNumeral M 0 = (0:M) from rfl,add_zero,a,argsAfter,if_true]
        change v = F subCode ![n,j+1]
        rw [hv]
        exact (modelSubAdd (j+1) v).symm
      · simp only [tick,out,Function.update_of_ne hi,a,argsAfter,hi,if_false,mul_add,mul_one]
        rw [add_assoc]
    apply PA194PausedReach.append PA194AX11HSource.step (t := sourceState first out tail)
    · apply PA194PausedReach.oneStep
      exact hs
    · change PA194PausedReach.Reaches PA194AX11HSource.step _ (sourceState site (a (j+1)) tail)
      rw [←ht]
      exact incrementsRun loop out tail
  have hrun := PA194PausedReach.runMany PA194AX11HSource.step frame n hf stepLoop n le_rfl
  change PA194PausedReach.Reaches PA194AX11HSource.step (sourceState site (a 0) tail) (sourceState site (a n) tail) at hrun
  rw [show a 0 = args from partialZero args r rs] at hrun
  have hz : a n (location r) = (0 : M) := by
    simp only [a,argsAfter,if_true]
    exact subSelf _
  apply PA194PausedReach.append PA194AX11HSource.step hrun
  apply PA194PausedReach.oneStep
  exact PA194AX11HSourceAt.sourceDecZero site exit r (some first) valid entry (a n) tail hz

#print axioms incrementsRun
#print axioms drain
end models
end PA194AX11HCandidateDrain
