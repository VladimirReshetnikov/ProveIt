import PA194M5FetchAgree
import PA194PausedReach
import PA194SourceFetchRestoreLoop
set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194M5FetchRestore
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation
open PA194SourceFetchLoop PA194SourceFetchRestoreLoop PA194ModelMPDrain PA194PausedReach
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

/-- Restore the fresh-fetch counter through candidate source sites 31–33,
for any model-valued counter. -/
theorem restore (args : Fin 11 → M) (tail : M) :
    PA194PausedReach.Reaches (PA194ProgramDrain.step PA194M5Program.program) (sourceState 31 args tail)
      (sourceState 34 (Function.update (Function.update args 0 (args 0 + args 6 + 1)) 6 0) tail) := by
  let n := args 6
  let a := argsAfter args 6 [0]
  let frame := fun j => sourceState 31 (a j) tail
  have hf : 𝚺₁-Function₁ frame := frameDef 31 (fun i j => a j i) tail (partialDef args 6 [0])
  have hstep (j : M) (hj : j < n) : PA194PausedReach.Reaches (PA194ProgramDrain.step PA194M5Program.program) (frame j) (frame (j+1)) := by
    obtain ⟨v,hv⟩ := le_iff_exists_add.mp (lt_iff_succ_le.mp hj)
    have hbefore : a j (location 6) = v+1 := by
      simp only [a,argsAfter,if_true]
      change F subCode ![n,j] = v+1
      rw [hv,show (j+1)+v = j+(v+1) by ac_rfl]
      exact modelSubAdd j (v+1)
    have hafter : F subCode ![n,j+1] = v := by
      rw [hv]
      exact modelSubAdd (j+1) v
    let b := Function.update (a j) 0 ((a j) 0+1)
    let c := Function.update b 6 v
    have h31 := sourceInc 31 32 0 (by decide) inst31 (a j) tail
    have h6 : regsOfArgs b 6 = v+1 := by simpa [b,regsOfArgs,location] using hbefore
    have h32 := sourceDecPositive 32 33 6 (some 34) (by decide) inst32 b tail v h6
    have h33 := sourceJump 33 31 (by decide) inst33 c tail
    have hafter' : F subCode ![args 6,j+1] = v := by simpa [n] using hafter
    have hc : c = a (j+1) := by
      funext i
      fin_cases i <;> simp [c,b,a,argsAfter,location,tally,hafter',
        PA194StateOne.modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl,add_assoc]
    have e31 : F (PA194ProgramDrain.step PA194M5Program.program) ![sourceState 31 (a j) tail] = sourceState 32 b tail := by
      rw [PA194M5FetchAgree.agrees 31 (by decide) (a j) tail]
      exact h31
    have e32 : F (PA194ProgramDrain.step PA194M5Program.program) ![sourceState 32 b tail] = sourceState 33 c tail := by
      rw [PA194M5FetchAgree.agrees 32 (by decide) b tail]
      exact h32
    have e33 : F (PA194ProgramDrain.step PA194M5Program.program) ![sourceState 33 c tail] = sourceState 31 c tail := by
      rw [PA194M5FetchAgree.agrees 33 (by decide) c tail]
      exact h33
    change PA194PausedReach.Reaches (PA194ProgramDrain.step PA194M5Program.program) (sourceState 31 (a j) tail) (sourceState 31 (a (j+1)) tail)
    rw [←hc]
    exact PA194PausedReach.append _ (PA194PausedReach.oneStep _ e31)
      (PA194PausedReach.append _ (PA194PausedReach.oneStep _ e32) (PA194PausedReach.oneStep _ e33))
  have hr := PA194PausedReach.runMany (PA194ProgramDrain.step PA194M5Program.program) frame n hf hstep n le_rfl
  change PA194PausedReach.Reaches (PA194ProgramDrain.step PA194M5Program.program) (sourceState 31 (a 0) tail) (sourceState 31 (a n) tail) at hr
  rw [show a 0 = args from partialZero args 6 [0]] at hr
  let b := Function.update (a n) 0 ((a n) 0+1)
  have h31 := sourceInc 31 32 0 (by decide) inst31 (a n) tail
  have h6 : regsOfArgs b 6 = 0 := by simp [b,regsOfArgs,a,n,argsAfter,location,subSelf]
  have h32 := sourceDecZero 32 34 6 (some 33) (by decide) inst32 b tail h6
  have hb : b = Function.update (Function.update args 0 (args 0 + args 6 + 1)) 6 0 := by
    funext i
    fin_cases i <;> simp [b,a,n,argsAfter,location,tally,subSelf,
      PA194StateOne.modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl,add_assoc]
  have e31 : F (PA194ProgramDrain.step PA194M5Program.program) ![sourceState 31 (a n) tail] = sourceState 32 b tail := by
    rw [PA194M5FetchAgree.agrees 31 (by decide) (a n) tail]
    exact h31
  have e32 : F (PA194ProgramDrain.step PA194M5Program.program) ![sourceState 32 b tail] = sourceState 34 b tail := by
    rw [PA194M5FetchAgree.agrees 32 (by decide) b tail]
    exact h32
  rw [←hb]
  exact PA194PausedReach.append _ hr
    (PA194PausedReach.append _ (PA194PausedReach.oneStep _ e31) (PA194PausedReach.oneStep _ e32))

#print axioms restore
end models
end PA194M5FetchRestore
