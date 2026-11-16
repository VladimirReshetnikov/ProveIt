import PA194Site25Then27Then28
import PA194StartupSourceFrame
import PA194Path27Frame
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SeedControllerReach29
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite25Physical
open PA194Site28OutputFile PA194SourceSite28Physical PA194Site25Then27Then28
open PA194StartupSourceFrame PA194RegisterPermutation PA194ZeroRuns PA194Path27Header PA194StateOne PA194FiniteControls
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem blankAndThreeSteps (tail : M) :
    let e : Fin 11 → M := fun i => modelNumeral M (seedArgs i)
    let k : M := modelNumeral M 39
    let finalArgs := updated (Function.update e 0 (1 : M))
    F step ![F step ![F step ![sourceState 25 e tail]]] = sourceState 29 finalArgs tail ∧
    ∃ clock : M, F PA194Stepper.stepper ![clock,modelNumeral M 0] =
      physicalFrame 29 (k+1) finalArgs := by
  let e : Fin 11 → M := fun i => modelNumeral M (seedArgs i)
  let k : M := modelNumeral M 39
  have hz : e 8 = (0 : M) := rfl
  have hp : e 0 = (1 : M)+(1 : M) := by
    change modelNumeral M 2 = (1 : M)+(1 : M)
    rw [←modelNumeralOne,←modelNumeralAdd]
  have ht : e 10 = modelNumeral M seedTail := rfl
  have hn : ((k+1)+1)+1 = modelNumeral M 42 := by
    dsimp only [k]
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd]
  have hstart := PA194StartupSourceFrame.modelDenseStartupSourceFrame (M := M)
  let z : M := (F sourceFileCode e)+(F sourceFileCode e)+1
  have hs (n : Nat) : F zeros ![modelNumeral M (n+1),z] =
      F zeros ![modelNumeral M n,z]+F zeros ![modelNumeral M n,z] := by
    have h := modelZerosSucc (M := M) (modelNumeral M n) z
    change F zeros ![F Code.succ (fun _ => modelNumeral M n),z] = _ at h
    rw [←modelAddOne] at h
    change F zeros ![(modelNumeral M n)+(1 : M),z] = _ at h
    rw [←modelNumeralOne,←modelNumeralAdd] at h
    exact h
  have hword : modelWord (PA194SourceProgram.path 25) (F zeros ![modelNumeral M 42,z]) =
      (F zeros ![modelNumeral M 47,z])+(F zeros ![modelNumeral M 47,z])+1 := by
    rw [PA194Path27Frame.path25]
    simp only [modelWord,Bool.false_eq_true,↓reduceIte,hs 46,hs 45,hs 44,hs 43,hs 42]
  have hf : physicalFrame 25 (((k+1)+1)+1) e =
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),
        (F zeros ![modelNumeral M 47,z])+(F zeros ![modelNumeral M 47,z])+1]] := by
    rw [hn]
    unfold physicalFrame
    dsimp only
    have ha : (1 : M)+((F sourceFileCode e)+(F sourceFileCode e)) = z := by
      dsimp only [z]
      exact add_comm _ _
    rw [ha,hword]
  change F PA194Stepper.stepper ![modelNumeral M 58154,modelNumeral M 0] = _ at hstart
  rw [modelNumeralOne,←hf] at hstart
  obtain ⟨hsource,c,hphysical⟩ := zeroPositiveIncrement k tail (1 : M) e hz hp ht
  refine ⟨hsource,F addCode ![modelNumeral M 58154,c],?_⟩
  rw [PA194StepperCompose.modelStepperCompose,hstart,hphysical]
#print axioms blankAndThreeSteps
end models
end PA194SeedControllerReach29
