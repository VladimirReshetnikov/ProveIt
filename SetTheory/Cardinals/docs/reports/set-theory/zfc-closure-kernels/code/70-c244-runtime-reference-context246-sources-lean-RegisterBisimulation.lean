import Init

/-!
Deterministic register-operation bisimulation, independent of decoder paths.

A program contains actual increment, zero/positive decrement, and halt
instructions. A relation matching operation labels and both decrement
successors preserves finite halting from every common register vector.

`run` counts attempted operations: a halt instruction returns `none` on the
next attempt. No theorem here identifies an exposed instruction with a DAG
control path, verifies a particular finite certificate, or simulates a binary
Turing machine. Those are separate interfaces for a future certificate port.
-/

namespace SetTheory.BusyBeaver.ZFC.RegisterBisimulation

universe u v

abbrev Registers := Nat → Nat

inductive Instruction (State : Type u) where
  | inc (register : Nat) (next : State)
  | dec (register : Nat) (zero positive : State)
  | halt

abbrev Program (State : Type u) := State → Instruction State

structure Configuration (State : Type u) where
  state : State
  registers : Registers

def writeRegister (r : Registers) (i value : Nat) : Registers :=
  fun j => if j = i then value else r j

/-- Zero decrements leave the vector unchanged; positive decrements subtract
one and follow the positive successor. -/
def step {State : Type u} (p : Program State)
    (c : Configuration State) : Option (Configuration State) :=
  match p c.state with
  | .inc i next =>
      some ⟨next, writeRegister c.registers i (c.registers i + 1)⟩
  | .dec i zero positive =>
      match c.registers i with
      | 0 => some ⟨zero, c.registers⟩
      | n + 1 => some ⟨positive, writeRegister c.registers i n⟩
  | .halt => none

def run {State : Type u} (p : Program State) :
    Nat → Configuration State → Option (Configuration State)
  | 0, c => some c
  | n + 1, c =>
      match step p c with
      | none => none
      | some next => run p n next

def Halts {State : Type u} (p : Program State)
    (c : Configuration State) : Prop :=
  ∃ n, run p n c = none

/-- Matching instructions use exactly the same register index. Both exits of
each conditional decrement must belong to the state relation. -/
def InstructionRelated {Left : Type u} {Right : Type v}
    (relation : Left → Right → Prop) :
    Instruction Left → Instruction Right → Prop
  | .inc i next, .inc j next' => i = j ∧ relation next next'
  | .dec i zero positive, .dec j zero' positive' =>
      i = j ∧ relation zero zero' ∧ relation positive positive'
  | .halt, .halt => True
  | _, _ => False

def Matches {Left : Type u} {Right : Type v}
    (p : Program Left) (q : Program Right)
    (relation : Left → Right → Prop) : Prop :=
  ∀ left right, relation left right →
    InstructionRelated relation (p left) (q right)

def ConfigurationRelated {Left : Type u} {Right : Type v}
    (relation : Left → Right → Prop)
    (left : Configuration Left) (right : Configuration Right) : Prop :=
  relation left.state right.state ∧ left.registers = right.registers

def ResultRelated {Left : Type u} {Right : Type v}
    (relation : Left → Right → Prop) :
    Option (Configuration Left) → Option (Configuration Right) → Prop
  | none, none => True
  | some left, some right => ConfigurationRelated relation left right
  | _, _ => False

theorem step_related {Left : Type u} {Right : Type v}
    {p : Program Left} {q : Program Right} {relation : Left → Right → Prop}
    (hMatches : Matches p q relation)
    {left : Configuration Left} {right : Configuration Right}
    (related : ConfigurationRelated relation left right) :
    ResultRelated relation (step p left) (step q right) := by
  rcases left with ⟨left, registers⟩
  rcases right with ⟨right, registers'⟩
  rcases related with ⟨states, vectors⟩
  change registers = registers' at vectors
  subst registers'
  have instructions := hMatches left right states
  cases hp : p left with
  | inc i next =>
      cases hq : q right with
      | inc j next' =>
          simp only [hp, hq, InstructionRelated] at instructions
          rcases instructions with ⟨rfl, successors⟩
          simpa only [step, hp, hq, ResultRelated, ConfigurationRelated]
            using And.intro successors
              (Eq.refl (writeRegister registers i (registers i + 1)))
      | dec j zero positive =>
          simp only [hp, hq, InstructionRelated] at instructions
      | halt =>
          simp only [hp, hq, InstructionRelated] at instructions
  | dec i zero positive =>
      cases hq : q right with
      | inc j next =>
          simp only [hp, hq, InstructionRelated] at instructions
      | dec j zero' positive' =>
          simp only [hp, hq, InstructionRelated] at instructions
          rcases instructions with ⟨rfl, zeros, positives⟩
          cases read : registers i with
          | zero =>
              simpa only [step, hp, hq, read, ResultRelated, ConfigurationRelated]
                using And.intro zeros (Eq.refl registers)
          | succ n =>
              simpa only [step, hp, hq, read, ResultRelated, ConfigurationRelated]
                using And.intro positives (Eq.refl (writeRegister registers i n))
      | halt =>
          simp only [hp, hq, InstructionRelated] at instructions
  | halt =>
      cases hq : q right with
      | inc j next =>
          simp only [hp, hq, InstructionRelated] at instructions
      | dec j zero positive =>
          simp only [hp, hq, InstructionRelated] at instructions
      | halt =>
          simp only [step, hp, hq, ResultRelated]

theorem run_related {Left : Type u} {Right : Type v}
    {p : Program Left} {q : Program Right} {relation : Left → Right → Prop}
    (hMatches : Matches p q relation) (n : Nat)
    {left : Configuration Left} {right : Configuration Right}
    (related : ConfigurationRelated relation left right) :
    ResultRelated relation (run p n left) (run q n right) := by
  induction n generalizing left right with
  | zero => exact related
  | succ n ih =>
      have steps := step_related hMatches related
      cases hp : step p left with
      | none =>
          cases hq : step q right with
          | none => simp only [run, hp, hq, ResultRelated]
          | some next =>
              simp only [hp, hq, ResultRelated] at steps
      | some next =>
          cases hq : step q right with
          | none =>
              simp only [hp, hq, ResultRelated] at steps
          | some next' =>
              simp only [hp, hq, ResultRelated] at steps
              simpa only [run, hp, hq] using ih steps

theorem related_none_iff {Left : Type u} {Right : Type v}
    {relation : Left → Right → Prop}
    {left : Option (Configuration Left)} {right : Option (Configuration Right)}
    (related : ResultRelated relation left right) :
    left = none ↔ right = none := by
  cases left <;> cases right <;> simp_all [ResultRelated]

/-- Matching exposed operations halt at the same finite attempted-operation
count. This theorem does not count contracted decoder/control steps. -/
theorem run_none_iff {Left : Type u} {Right : Type v}
    {p : Program Left} {q : Program Right} {relation : Left → Right → Prop}
    (hMatches : Matches p q relation) (n : Nat)
    {left : Configuration Left} {right : Configuration Right}
    (related : ConfigurationRelated relation left right) :
    run p n left = none ↔ run q n right = none :=
  related_none_iff (run_related hMatches n related)

theorem halts_iff {Left : Type u} {Right : Type v}
    {p : Program Left} {q : Program Right} {relation : Left → Right → Prop}
    (hMatches : Matches p q relation)
    {left : Configuration Left} {right : Configuration Right}
    (related : ConfigurationRelated relation left right) :
    Halts p left ↔ Halts q right := by
  constructor
  · rintro ⟨n, halted⟩
    exact ⟨n, (run_none_iff hMatches n related).mp halted⟩
  · rintro ⟨n, halted⟩
    exact ⟨n, (run_none_iff hMatches n related).mpr halted⟩

/-- The register vector is arbitrary, including data retained from a previous
candidate. It need not be blank, bounded, or reachable from an initializer. -/
theorem halts_from_any_registers {Left : Type u} {Right : Type v}
    {p : Program Left} {q : Program Right} {relation : Left → Right → Prop}
    (hMatches : Matches p q relation) {left : Left} {right : Right}
    (initial : relation left right) (registers : Registers) :
    Halts p ⟨left, registers⟩ ↔ Halts q ⟨right, registers⟩ :=
  halts_iff hMatches ⟨initial, rfl⟩

theorem halts_from_zero_registers {Left : Type u} {Right : Type v}
    {p : Program Left} {q : Program Right} {relation : Left → Right → Prop}
    (hMatches : Matches p q relation) {left : Left} {right : Right}
    (initial : relation left right) :
    Halts p ⟨left, fun _ => 0⟩ ↔ Halts q ⟨right, fun _ => 0⟩ :=
  halts_from_any_registers hMatches initial (fun _ => 0)

#print axioms step_related
#print axioms run_related
#print axioms halts_iff
#print axioms halts_from_any_registers

end SetTheory.BusyBeaver.ZFC.RegisterBisimulation
