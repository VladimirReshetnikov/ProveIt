import PA194SourceInstructionModel
import PA194SourceRegisterRelation
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SourceInstructionCalibration
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SourceInstructionModel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def execute (i : Option M6.Source.Instruction) (regs : Fin 9 → M) : Nat × (Fin 9 → M) :=
  match i with
  | none => (3673,regs)
  | some (.inc r next) => (destination next, Function.update regs r (F Code.succ (fun _ => regs r)))
  | some (.dec r zero positive) =>
      if regs r = (0 : M) then (destination zero,regs)
      else (destination positive,Function.update regs r (F predCode (fun _ => regs r)))
  | some (.jump next) => (destination next,regs)
  | some .halt => (3674,regs)

theorem instructionCalibration (i : Option M6.Source.Instruction) (s : M)
    (regs : Fin 9 → M) (h : Encodes (pi₂ s) regs) :
    pi₁ (instructionSem i s) = modelNumeral M (execute i regs).1 ∧
      Encodes (pi₂ (instructionSem i s)) (execute i regs).2 := by
  classical
  cases i with
  | none =>
    simp only [instructionSem,execute,pi₁_pair,pi₂_pair, true_and]
    exact h
  | some i =>
    cases i with
    | inc r next =>
      simp only [instructionSem,execute,pi₁_pair,pi₂_pair]
      rw [h r]
      exact ⟨trivial,updateEncodes _ _ h r _⟩
    | dec r zero positive =>
      by_cases hz : regs r = (0 : M)
      · have hz' : getSem r.val (pi₂ s) = (0 : M) := (h r).trans hz
        simp only [instructionSem,execute,hz',hz,if_true,pi₁_pair,pi₂_pair]
        exact ⟨trivial,h⟩
      · have hz' : getSem r.val (pi₂ s) ≠ (0 : M) := by simpa [h r] using hz
        simp only [instructionSem,execute,hz',hz,if_false,pi₁_pair,pi₂_pair]
        rw [h r]
        exact ⟨trivial,updateEncodes _ _ h r _⟩
    | jump next =>
      simp only [instructionSem,execute,pi₁_pair,pi₂_pair, true_and]
      exact h
    | halt =>
      simp only [instructionSem,execute,pi₁_pair,pi₂_pair, true_and]
      exact h
#print axioms instructionCalibration
end models
end PA194SourceInstructionCalibration
