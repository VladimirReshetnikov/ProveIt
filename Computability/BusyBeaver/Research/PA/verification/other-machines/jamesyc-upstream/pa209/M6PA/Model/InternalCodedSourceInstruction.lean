module
public import M6PA.Model.PATheory
public import M6PA.Model.InternalCodedSourceRegisters
public import M6PA.Model.InternalModelSource
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.Arithmetic.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def destinationCode : Option Nat → Nat
  | none => 1
  | some i => i+1

/-- Distinct halt and malformed codes; actual working ordinals are 0..3946. -/
def controlCode : Source.Control → Nat
  | .at i => i+1
  | .halted => 0
  | .exited => 1
  | .malformed => 3948

def instructionGraph : Source.Instruction → 𝚺ᴬ₁.Semisentence 2
  | .inc r n => .mkSigma “y xs. ∃ a rs, !(FileBoxes.valueGraph r.val) a xs ∧
      !(replaceGraph r.val) rs xs (a+1) ∧ !adjoinDef y ↑(destinationCode n) rs”
  | .dec r z n => .mkSigma “y xs. ∃ a, !(FileBoxes.valueGraph r.val) a xs ∧
      ((a=0 ∧ !adjoinDef y ↑(destinationCode z) xs) ∨
       (a≠0 ∧ ∃ b rs, !subDef b a 1 ∧ !(replaceGraph r.val) rs xs b ∧
         !adjoinDef y ↑(destinationCode n) rs))”
  | .jump n => .mkSigma “y xs. !adjoinDef y ↑(destinationCode n) xs”
  | .halt => .mkSigma “y xs. !adjoinDef y 0 xs”
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def instructionValue (i : Source.Instruction) (xs : V) : V :=
  match i with
  | .inc r n => stateCode (destinationCode n) (replace r.val xs (registers xs r+1))
  | .dec r z n => if registers xs r=0 then stateCode (destinationCode z) xs
      else stateCode (destinationCode n) (replace r.val xs (registers xs r-1))
  | .jump n => stateCode (destinationCode n) xs
  | .halt => stateCode 0 xs

instance instruction_defined (i : Source.Instruction) :
    𝚺ᴬ₁-Function₁ (instructionValue i : V → V) via instructionGraph i := by
  cases i with
  | inc r n => exact .mk fun v => by simp [instructionGraph,(FileBoxes.value_defined r.val).df,
      (replace_defined r.val).df,adjoin_defined.df,numeral_eq_natCast,instructionValue,
      stateCode,registers,FileLayout.value_nth]
  | dec r z n =>
    exact .mk fun v => by
      simp [instructionGraph,(FileBoxes.value_defined r.val).df,(replace_defined r.val).df,
        adjoin_defined.df,sub_defined.df,numeral_eq_natCast,instructionValue,stateCode,
        registers,FileLayout.value_nth]
      split_ifs <;> simp_all
  | jump n => exact .mk fun v => by simp [instructionGraph,adjoin_defined.df,
      numeral_eq_natCast,instructionValue,stateCode]
  | halt => exact .mk fun v => by simp [instructionGraph,adjoin_defined.df,instructionValue,stateCode]

theorem instruction_store_valid (i : Source.Instruction) (xs : V) (h : ValidStore xs) :
    ValidStore (store (instructionValue i xs)) := by
  cases i with
  | inc r n => simpa only [instructionValue,store_state] using replace_valid xs _ h r
  | dec r z n => simp only [instructionValue]; split_ifs <;>
      simp only [store_state] <;> first | exact h | exact replace_valid xs _ h r
  | jump n => simpa only [instructionValue,store_state] using h
  | halt => simpa only [instructionValue,store_state] using h

theorem instruction_total_unique (i : Source.Instruction) (xs : V) :
    ∃! y, V ⊧/![y,xs] (instructionGraph i).val := by
  refine ⟨instructionValue i xs,?_,?_⟩
  · exact ((instruction_defined i).df _).mpr rfl
  · intro y hy
    exact ((instruction_defined i).df _).mp hy
/-- Exact calibration to the already defined arbitrary-model literal instruction,
including cyclic restart. This is stronger than standard-Nat-only calibration. -/
theorem instruction_calibration (i : Source.Instruction) (xs : V) (h : ValidStore xs) :
    control (instructionValue i xs)=
      (controlCode (ModelSource.restart (ModelSource.execute i (registers xs))).control : V) ∧
    registers (store (instructionValue i xs))=
      (ModelSource.restart (ModelSource.execute i (registers xs))).registers := by
  cases i with
  | inc r n => cases n <;> simp [instructionValue,ModelSource.execute,ModelSource.restart,
      Source.destination,controlCode,destinationCode,registers_replace xs _ h]
  | dec r z n =>
    by_cases hz : registers xs r=0 <;> cases z <;> cases n <;>
      simp [instructionValue,ModelSource.execute,ModelSource.restart,Source.destination,
        controlCode,destinationCode,hz,registers_replace xs _ h]
  | jump n => cases n <;> simp [instructionValue,ModelSource.execute,ModelSource.restart,
      Source.destination,controlCode,destinationCode]
  | halt => simp [instructionValue,ModelSource.execute,ModelSource.restart,controlCode]

end Models
#print axioms instruction_defined
#print axioms instruction_store_valid
#print axioms instruction_calibration
#print axioms instruction_total_unique
end M6.Arithmetic.PA.InternalTrace.CodedSource

