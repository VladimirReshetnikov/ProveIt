import PA194SourceReachable
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SourceNoMalformed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PA194FiniteControls PA194StateOne
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation
open PA194SourceInstructionCalibration PA194SourceBoundedStep PA194SourceTargetBounds PA194SourcePCBound
open PA194SourceSentinel PA194ClockInvariantDefinable PA194IteratedSimulation

def AllResolved : Prop := ∀ i : Nat, i < 3673 → ∃ inst, M6.Source.resolveAt PA194SourceProgram.sites i = some inst

theorem destinationWorking (n : Option Nat) (h : DestinationBound 3673 n) : destination n < 3673 := by
  cases n with
  | none => decide
  | some j => exact h j rfl

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem executeWorkingOrHalt (inst : M6.Source.Instruction) (regs : Fin 9 → M)
    (h : InstructionBound 3673 inst) :
    (execute (some inst) regs).1 < 3673 ∨ (execute (some inst) regs).1 = 3674 := by
  classical
  cases inst with
  | inc r next => exact Or.inl (destinationWorking next h)
  | dec r zero positive =>
    change (if regs r = (0 : M) then (destination zero,regs)
      else (destination positive,Function.update regs r (F predCode (fun _ => regs r)))).1 < 3673 ∨ _
    split_ifs
    · exact Or.inl (destinationWorking zero h.1)
    · exact Or.inl (destinationWorking positive h.2)
  | jump next => exact Or.inl (destinationWorking next h)
  | halt => right; rfl

theorem stepWorkingOrHalt (resolved : AllResolved) (s : M)
    (hpc : F pc ![s] < modelNumeral M 3673) :
    F pc ![F step ![s]] < modelNumeral M 3673 ∨ F pc ![F step ![s]] = modelNumeral M 3674 := by
  let regs : Fin 9 → M := fun r => getSem r.val (pi₂ s)
  have hr : Encodes (pi₂ s) regs := by intro r; rfl
  obtain ⟨i,_,hstep,_⟩ := boundedStepCalibration s regs hpc hr
  obtain ⟨inst,hinst⟩ := resolved i.val i.isLt
  have hi : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie i.val).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some inst := by
    rw [←PA194SourceProgram.resolve_tree]
    exact hinst
  rw [hi] at hstep
  have hb := literalInstructionBound i.val inst hinst
  rcases executeWorkingOrHalt inst regs hb with hw | hh
  · left; rw [pcModel,hstep]; exact modelNumeralStrict _ _ hw
  · right; rw [pcModel,hstep,hh]

theorem stepValidPC (resolved : AllResolved) (s : M)
    (hs : F pc ![s] < modelNumeral M 3673 ∨ F pc ![s] = modelNumeral M 3674) :
    F pc ![F step ![s]] < modelNumeral M 3673 ∨ F pc ![F step ![s]] = modelNumeral M 3674 := by
  rcases hs with hw | hh
  · exact stepWorkingOrHalt resolved s hw
  · rw [stepHalted s hh]
    exact Or.inr hh

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem runValidPC (resolved : AllResolved) (seed : M)
    (hseed : F pc ![seed] < modelNumeral M 3673 ∨ F pc ![seed] = modelNumeral M 3674) :
    ∀ n : M, F pc ![F run ![n,seed]] < modelNumeral M 3673 ∨
      F pc ![F run ![n,seed]] = modelNumeral M 3674 := by
  have hr : 𝚺₁-Function₁ (fun n : M => F run ![n,seed]) :=
    bindBinary _ seed (binaryCodeDef (M := M) run)
  have hq : 𝚺₁-Function₁ (fun n : M => F pc ![F run ![n,seed]]) :=
    composeUnary _ _ (unaryCodeDef (M := M) pc) hr
  haveI := hq
  have hp : 𝚺₁-Predicate (fun n : M => F pc ![F run ![n,seed]] < modelNumeral M 3673 ∨
      F pc ![F run ![n,seed]] = modelNumeral M 3674) := by definability
  intro n
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact hp
  | zero => rw [run,iterateZero]; exact hseed
  | succ n ih => rw [run,iterateSucc]; exact stepValidPC resolved _ ih
#print axioms stepWorkingOrHalt
#print axioms stepValidPC
#print axioms runValidPC
end models
end PA194SourceNoMalformed
