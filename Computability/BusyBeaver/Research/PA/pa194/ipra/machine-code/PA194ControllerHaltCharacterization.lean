import PA194SourceNoMalformed
import PA194SourceHaltUnique
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ControllerHaltCharacterization
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PA194FiniteControls PA194StateOne
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters PA194SourceRegisterRelation
open PA194SourceInstructionCalibration PA194SourceBoundedStep PA194SourceTargetBounds PA194SourcePCBound
open PA194SourceNoMalformed PA194SourceHaltUnique
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem executeHaltOnly (inst : M6.Source.Instruction) (regs : Fin 9 → M)
    (hb : InstructionBound 3673 inst)
    (h : (execute (some inst) regs).1 = 3674) : inst = .halt := by
  classical
  cases inst with
  | inc r next =>
    exfalso
    have hh := destinationWorking next hb
    change destination next = 3674 at h
    omega
  | dec r z p =>
    exfalso
    change (if regs r = (0 : M) then (destination z,regs)
      else (destination p,Function.update regs r (F predCode (fun _ => regs r)))).1 = 3674 at h
    split_ifs at h
    · have hh := destinationWorking z hb.1; omega
    · have hh := destinationWorking p hb.2; omega
  | jump next =>
    exfalso
    have hh := destinationWorking next hb
    change destination next = 3674 at h
    omega
  | halt => rfl

theorem nextHaltIffSite10 (s : M) (hpc : F pc ![s] < modelNumeral M 3673) :
    F pc ![F step ![s]] = modelNumeral M 3674 ↔ F pc ![s] = modelNumeral M 10 := by
  constructor
  · intro hnext
    let regs : Fin 9 → M := fun r => getSem r.val (pi₂ s)
    have hr : Encodes (pi₂ s) regs := by intro r; rfl
    obtain ⟨i,hi,hstep,_⟩ := boundedStepCalibration s regs hpc hr
    have hstep' : F pc ![F step ![s]] = modelNumeral M
      (execute (M6.Source.resolveAt PA194SourceProgram.sites i.val) regs).1 := by
      rw [pcModel,PA194SourceProgram.resolve_tree]
      exact hstep
    cases hinst : M6.Source.resolveAt PA194SourceProgram.sites i.val with
    | none =>
      rw [hinst] at hstep'
      have hc : modelNumeral M 3673 = modelNumeral M 3674 := by
        change F pc ![F step ![s]] = modelNumeral M 3673 at hstep'
        exact hstep'.symm.trans hnext
      exact False.elim ((ne_of_lt (modelNumeralStrict 3673 3674 (by decide))) hc)
    | some inst =>
      have hb := literalInstructionBound i.val inst hinst
      rcases executeWorkingOrHalt inst regs hb with hw | hh
      · rw [hinst] at hstep'
        have heq : modelNumeral M (execute (some inst) regs).1 = modelNumeral M 3674 := hstep'.symm.trans hnext
        have hlt := modelNumeralStrict (M := M) (execute (some inst) regs).1 3673 hw
        have hlt2 := modelNumeralStrict (M := M) 3673 3674 (by decide)
        exact False.elim ((ne_of_lt (lt_trans hlt hlt2)) heq)
      · have hit := executeHaltOnly inst regs hb hh
        subst inst
        have hindex : i.val=10 := resolvedHaltIndex i.val hinst
        simpa [hindex] using hi
  · intro hs
    rw [site10Step s hs,pcModel,pi₁_pair]
#print axioms executeHaltOnly
#print axioms nextHaltIffSite10
end models
end PA194ControllerHaltCharacterization
