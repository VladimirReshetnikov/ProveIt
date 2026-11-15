import PA194SourceBoundedStep
import PA194SourceTargetBounds
import PA194StateOne
import PackedDecoderModel
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SourcePCBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PackedClock PackedDecoderModel PA194StateOne
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation
open PA194SourceInstructionCalibration PA194SourceBoundedStep PA194SourceTargetBounds

def optionBound (i : Option M6.Source.Instruction) : Prop :=
  match i with
  | none => True
  | some inst => InstructionBound 3673 inst

theorem destinationLt (n : Option Nat) (h : DestinationBound 3673 n) : destination n < 3675 := by
  cases n with
  | none => decide
  | some j => have hj := h j rfl; simp only [destination]; omega

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem pcModel (s : M) : F pc ![s] = pi₁ s := by
  have hv : (![s] : Fin 1 → M) = fun _ => s := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [pc,hv,modelDecodeLeft]

theorem executeBound (i : Option M6.Source.Instruction) (regs : Fin 9 → M)
    (h : optionBound i) : (execute i regs).1 < 3675 := by
  classical
  cases i with
  | none => change 3673 < 3675; decide
  | some inst =>
    cases inst with
    | inc r next => exact destinationLt next h
    | dec r zero positive =>
      change (if regs r = (0 : M) then (destination zero,regs)
        else (destination positive,Function.update regs r (F predCode (fun _ => regs r)))).1 < 3675
      split_ifs
      · exact destinationLt zero h.1
      · exact destinationLt positive h.2
    | jump next => exact destinationLt next h
    | halt => change 3674 < 3675; decide

theorem stepWorkingPCBound (s : M)
    (hpc : F pc ![s] < modelNumeral M 3673) :
    F pc ![F step ![s]] < modelNumeral M 3675 := by
  let regs : Fin 9 → M := fun r => getSem r.val (pi₂ s)
  have hr : Encodes (pi₂ s) regs := by intro r; rfl
  obtain ⟨i,_,hstep,_⟩ := boundedStepCalibration s regs hpc hr
  let inst := (M6.Source.PathTrie.nthSite PA194.SourceTree.trie i.val).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie)
  have hb : optionBound inst := by
    have hresolve : M6.Source.resolveAt PA194SourceProgram.sites i.val = inst :=
      PA194SourceProgram.resolve_tree i.val
    cases hi : inst with
    | none => trivial
    | some ins =>
      apply literalInstructionBound i.val ins
      rw [hresolve,hi]
  rw [pcModel,hstep]
  exact modelNumeralStrict _ _ (executeBound inst regs hb)
#print axioms destinationLt
#print axioms executeBound
#print axioms stepWorkingPCBound
end models
end PA194SourcePCBound
