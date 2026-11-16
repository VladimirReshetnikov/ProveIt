module
public import M6.Source.ExactSource
public import M6PA.Model.PAInternalPhysicalRegisters
public import M6.Source.InstructionOutcome
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.ModelSource
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open M6.Runtime
structure Configuration (V : Type*) where
  control : Source.Control
  registers : Fin 9 → V
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
open PhysicalRegisters

/-- The same resolved source instruction syntax, interpreted over an arbitrary
PA model. This is not the four-field command-store encoding. -/
noncomputable def execute (i : Source.Instruction) (rs : Fin 9 → V) : Configuration V :=
  match i with
  | .inc r n => ⟨Source.destination n,write rs r (rs r+1)⟩
  | .dec r z n => if rs r=0 then ⟨Source.destination z,rs⟩
      else ⟨Source.destination n,write rs r (rs r-1)⟩
  | .jump n => ⟨Source.destination n,rs⟩
  | .halt => ⟨.halted,rs⟩

noncomputable def step (c : Configuration V) : Configuration V :=
  match c.control with
  | .at n => match Source.resolveAt Source.exactSites n with
      | some i => execute i c.registers
      | none => ⟨.malformed,c.registers⟩
  | _ => c

noncomputable def restart (c : Configuration V) : Configuration V :=
  match c.control with
  | .exited => ⟨.at 0,c.registers⟩
  | _ => c
noncomputable def cycleStep (c : Configuration V) : Configuration V := restart (step c)

/-- Full-file arithmetic interpretation of the already checked branch-sensitive
instruction outcome, preserving every unmodified logical and physical cell. -/
theorem outcome_sound (i : Source.Instruction) (br : Branch) (q : Source.Control) (e : Eff)
    (hi : Source.instructionOutcome i br=some (q,e)) (xs : V)
    (hsize : (10 : V)≤len xs) (hg : FileBoxes.Guard xs br) :
    execute i (readFile xs)=⟨q,readFile (FileEffects.effect e xs)⟩ := by
  cases i with
  | inc r n =>
    cases br with
    | some p => simp [Source.instructionOutcome] at hi
    | none =>
      simp only [Source.instructionOutcome,Option.some.injEq,Prod.mk.injEq] at hi
      obtain ⟨rfl,rfl⟩ := hi
      simp only [execute,read_increment xs hsize]
  | jump n =>
    cases br with
    | some p => simp [Source.instructionOutcome] at hi
    | none =>
      simp only [Source.instructionOutcome,Option.some.injEq,Prod.mk.injEq] at hi
      obtain ⟨rfl,rfl⟩ := hi
      rfl
  | halt =>
    cases br with
    | some p => simp [Source.instructionOutcome] at hi
    | none =>
      simp only [Source.instructionOutcome,Option.some.injEq,Prod.mk.injEq] at hi
      obtain ⟨rfl,rfl⟩ := hi
      rfl
  | dec r z n =>
    cases br with
    | none => simp [Source.instructionOutcome] at hi
    | some p =>
      rcases p with ⟨p,b⟩
      by_cases hp : p=Source.physicalRegister r
      · subst p
        cases b with
        | false =>
          simp only [Source.instructionOutcome,ne_eq,not_true_eq_false,ite_false,
            Option.some.injEq,Prod.mk.injEq] at hi
          obtain ⟨rfl,rfl⟩ := hi
          have hz : readFile xs r≠0 := by
            simpa only [FileBoxes.Guard,FileLayout.value_nth,readFile] using hg
          simp only [execute,if_neg hz,read_decrement xs hsize]
        | true =>
          simp only [Source.instructionOutcome,ne_eq,not_true_eq_false,ite_false,
            Option.some.injEq,Prod.mk.injEq] at hi
          obtain ⟨rfl,rfl⟩ := hi
          have hz : readFile xs r=0 := by
            simpa only [FileBoxes.Guard,FileLayout.value_nth,readFile] using hg
          simp only [execute,if_pos hz,FileEffects.effect]
      · simp [Source.instructionOutcome,hp] at hi
end Models
#print axioms outcome_sound
end M6.Arithmetic.PA.InternalTrace.ModelSource

