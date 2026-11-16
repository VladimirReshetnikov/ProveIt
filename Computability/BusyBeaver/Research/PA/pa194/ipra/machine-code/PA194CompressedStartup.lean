import PA194CompressedSourceFrame
import PA194OneSpareSeed2
import PA194Path27Frame

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194CompressedStartup
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing TableDispatch PA194FiniteControls PA194StateOne
open PA194StartupSourceFrame PA194CompressedSourceFrame
open PA194SourceSite31Controller PA194SourceSite31Physical PA194SourceRegisters PA194SourceRegisterRelation
open PA194SourceControllerCode PA194SourceControllerStep PA194IteratedSimulation
open PA194SourcePCBound (pcModel)
open PA194Path27Header PA194BidirectionalRunScan PA194CompressedRunAlgebra
open PA194SymbolicMove PA194BidirectionalRow PA194ZeroRuns

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def startArgs : Fin 11 → M := fun i => modelNumeral M (seedArgs i)
noncomputable def initialSource : M := sourceState 25 startArgs (0 : M)
noncomputable def initialSpare : M := startArgs (M := M) 9

theorem initialPC : F pc ![(initialSource : M)] = modelNumeral M 25 := by
  rw [pcModel]
  exact pi₁_pair _ _

theorem seedArguments : args (initialSource : M) (modelNumeral M 25) initialSpare = startArgs := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [args,Fin.snoc_last]
    exact PA194OneSpareSeed2.modelSeed
  · refine Fin.lastCases ?_ (fun r => ?_) j
    · simp only [args,Fin.snoc_castSucc,Fin.snoc_last]
      rfl
    · simp only [args,Fin.snoc_castSucc]
      unfold initialSource sourceState
      rw [pi₂_pair]
      exact packEncodes (regsOfArgs startArgs) (0 : M) r

theorem blankWord (n : Nat) (x : M) :
    modelWord (List.replicate n false) x = F zeros ![modelNumeral M n,x] := by
  induction n with
  | zero => exact (modelZerosZero x).symm
  | succ n ih =>
    rw [List.replicate_succ,wordPush,modelNumeralSucc]
    change push false (modelWord (List.replicate n false) x) =
      F (runCode false) ![modelNumeral M n+1,x]
    rw [runSucc,ih]
    rfl

theorem blankToRoot : F PA194Stepper.stepper ![modelNumeral M 58154,(0 : M)] =
    physicalFrame 25 (modelNumeral M 42) startArgs := by
  have h := modelDenseStartupSourceFrame (M := M)
  let f := F PA194RegisterPermutation.sourceFileCode (startArgs (M := M))
  let z : M := f+f+1
  change F PA194Stepper.stepper ![modelNumeral M 58154,(0 : M)] =
    F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,
      push true (F zeros ![modelNumeral M 47,z])]] at h
  rw [modelNumeralOne] at h
  unfold physicalFrame
  rw [PA194Path27Frame.path25]
  dsimp only
  rw [wordPush]
  have ha : (1 : M) + (f+f) = z := by unfold z; ac_rfl
  change F PA194Stepper.stepper ![modelNumeral M 58154,(0 : M)] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),
      push true (modelWord (List.replicate 5 false) (F zeros ![modelNumeral M 42,1+(f+f)]))]]
  rw [ha,blankWord]
  have hh := runAppend false (modelNumeral M 5) (modelNumeral M 42) z
  rw [←modelNumeralAdd] at hh
  change F zeros ![modelNumeral M 47,z] = F zeros ![modelNumeral M 5,F zeros ![modelNumeral M 42,z]] at hh
  rw [←hh]
  exact h

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem initialAligned :
    F pc ![F run ![(0 : M),initialSource]] < modelNumeral M 3673 ∧
      ∃ t gap count : M, 0 ≤ t ∧ F PA194Stepper.stepper ![t,(0 : M)] =
        F sourceRootCode ![F run ![(0 : M),initialSource],gap,count,initialSpare] := by
  have hs : F run ![(0 : M),initialSource] = initialSource := by
    unfold run
    rw [iterateZero]
  refine ⟨?_,modelNumeral M 58154,0,modelNumeral M 25,zero_le,?_⟩
  · rw [hs,initialPC]
    exact modelNumeralStrict 25 3673 (by decide)
  · rw [hs,sourceRootCodeCorrect _ _ _ _ ⟨25,by decide⟩ initialPC,seedArguments,zero_add]
    have hlen : 48-(PA194SourceProgram.path 25).length = 42 := by
      rw [PA194Path27Frame.path25]
      rfl
    change _ = physicalFrame 25 (modelNumeral M (48-(PA194SourceProgram.path 25).length)) startArgs
    rw [hlen]
    exact blankToRoot

#print axioms blankToRoot
#print axioms initialAligned
end models
end PA194CompressedStartup
