import PA194SourceActualStepCalibration
import M6.Source.CyclicDriver
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SourceStandardBinding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PA194SourceControllerCode PA194SourceInstructionCalibration
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language) (M := Nat)
local instance : Zero Nat := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One Nat := ⟨F oneCode Fin.elim0⟩
local instance : Add Nat := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul Nat := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT Nat := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : Nat↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

def ordinal : M6.Source.Control → Nat
  | .at i => i
  | .exited => 0
  | .malformed => 3673
  | .halted => 3674

def resolvedSource (i : Option M6.Source.Instruction) (regs : Fin 9 → Nat) : M6.Source.Configuration :=
  match i with
  | none => ⟨.malformed,regs⟩
  | some ins => M6.Source.restart (M6.Source.execute ins regs)

theorem natSucc (x : Nat) : F Code.succ (fun _ => x) = x+1 := by rfl

theorem natPred (x : Nat) : F predCode (fun _ => x) = x-1 := by
  change eval predCode (x ::ᵥ List.Vector.nil) = x-1
  simpa only [Nat.pred_eq_sub_one] using eval_predCode x

theorem writeEqUpdate (regs : Fin 9 → Nat) (r : Fin 9) (v : Nat) :
    M6.Source.write regs r v = Function.update regs r v := by
  funext j
  by_cases hj : j = r
  · subst j; simp [M6.Source.write]
  · simp [M6.Source.write,hj,Function.update_of_ne hj]

theorem resolvedBinding (i : Option M6.Source.Instruction) (regs : Fin 9 → Nat) :
    PA194SourceInstructionCalibration.execute i regs =
      (ordinal (resolvedSource i regs).control,(resolvedSource i regs).registers) := by
  cases i with
  | none => rfl
  | some i =>
    cases i with
    | inc r n =>
      cases n <;> simp [PA194SourceInstructionCalibration.execute,resolvedSource,
        M6.Source.execute,M6.Source.restart,M6.Source.destination,ordinal,destination,natSucc,writeEqUpdate] <;> rfl
    | dec r z n =>
      by_cases hz : regs r = 0 <;> cases z <;> cases n <;>
        simp [PA194SourceInstructionCalibration.execute,resolvedSource,
          M6.Source.execute,M6.Source.restart,M6.Source.destination,ordinal,destination,
          hz,natPred,writeEqUpdate] <;>
        intro h <;> exact False.elim (hz h)
    | jump n =>
      cases n <;> simp [PA194SourceInstructionCalibration.execute,resolvedSource,
        M6.Source.execute,M6.Source.restart,M6.Source.destination,ordinal,destination]
    | halt => rfl
theorem natNumeral (n : Nat) : TableDispatch.modelNumeral Nat n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [PA194FiniteControls.modelNumeralSucc,ih]; rfl

theorem resolvedSourceEqCycle (i : Nat) (regs : Fin 9 → Nat) :
    resolvedSource (M6.Source.resolveAt PA194SourceProgram.sites i) regs =
      M6.Source.cycleStep PA194SourceProgram.sites ⟨.at i,regs⟩ := by
  cases h : M6.Source.resolveAt PA194SourceProgram.sites i with
  | none => simp [resolvedSource,M6.Source.cycleStep,M6.Source.step,h,M6.Source.restart]
  | some ins => simp [resolvedSource,M6.Source.cycleStep,M6.Source.step,h]

/-- Standard-natural calibration of the actual PR controller step to the
    original source cycle step, from any valid standard source ordinal. -/
theorem actualStepCycle (i : Nat) (hi : i < 3673) (s : Nat) (regs : Fin 9 → Nat)
    (hpc : F pc ![s] = i)
    (hregs : PA194SourceRegisterRelation.Encodes (LO.FirstOrder.Arithmetic.pi₂ s) regs) :
    let target := M6.Source.cycleStep PA194SourceProgram.sites ⟨.at i,regs⟩
    LO.FirstOrder.Arithmetic.pi₁ (F step ![s]) = ordinal target.control ∧
      PA194SourceRegisterRelation.Encodes (LO.FirstOrder.Arithmetic.pi₂ (F step ![s])) target.registers := by
  have hs : F pc ![s] = TableDispatch.modelNumeral Nat i := by simpa [natNumeral] using hpc
  have h := PA194SourceActualStepCalibration.actualStepCalibration i hi s regs hs hregs
  dsimp only at h
  rw [← PA194SourceProgram.resolve_tree, resolvedBinding, resolvedSourceEqCycle] at h
  simpa only [Prod.fst,Prod.snd,natNumeral] using h
#print axioms actualStepCycle
#print axioms resolvedSourceEqCycle
#print axioms resolvedBinding
end PA194SourceStandardBinding
