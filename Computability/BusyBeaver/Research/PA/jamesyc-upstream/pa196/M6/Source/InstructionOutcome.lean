module
public import M6.Source.RootFrame
public import M6.Source.CyclicDriver
@[expose] public section

namespace M6.Source
open M6.Runtime

/-- Branch-sensitive logical instruction outcome with the exact physical-file
operation. A wrong physical register branch is rejected. -/
def instructionOutcome (i : Instruction) (branch : Branch) : Option (Control × Eff) :=
  match i, branch with
  | .inc r n, none => some (destination n, .inc (physicalRegister r))
  | .dec r z n, some (p,b) =>
      if p ≠ physicalRegister r then none
      else if b then some (destination z, .none)
      else some (destination n, .dec p)
  | .jump n, none => some (destination n, .none)
  | .halt, none => some (.halted, .none)
  | _, _ => none

/-- Projection of the complete physical file executes precisely one source
instruction, including both decrement branches and increment's new spare. -/
theorem instructionOutcome_sound (hi : instructionOutcome i br = some (q,e))
    (hv : Valid br vs) :
    execute i (readFile vs) = ⟨q, readFile (effectFile e vs)⟩ := by
  have hlen : 9 ≤ vs.length := by have := hv.1; omega
  cases i with
  | inc r n =>
    cases br with
    | some p => simp [instructionOutcome] at hi
    | none =>
      simp only [instructionOutcome, Option.some.injEq, Prod.mk.injEq] at hi
      rcases hi with ⟨rfl,rfl⟩
      simp only [execute, effectFile, readFile_increment_with_spare vs hlen]
  | jump n =>
    cases br with
    | some p => simp [instructionOutcome] at hi
    | none =>
      simp only [instructionOutcome, Option.some.injEq, Prod.mk.injEq] at hi
      rcases hi with ⟨rfl,rfl⟩
      rfl
  | halt =>
    cases br with
    | some p => simp [instructionOutcome] at hi
    | none =>
      simp only [instructionOutcome, Option.some.injEq, Prod.mk.injEq] at hi
      rcases hi with ⟨rfl,rfl⟩
      rfl
  | dec r z n =>
    cases br with
    | none => simp [instructionOutcome] at hi
    | some p =>
      rcases p with ⟨p,b⟩
      by_cases hp : p = physicalRegister r
      · subst p
        cases b with
        | false =>
          simp only [instructionOutcome, ne_eq, not_true_eq_false, ↓reduceIte,
            Option.some.injEq, Prod.mk.injEq] at hi
          rcases hi with ⟨rfl,rfl⟩
          have hz : readFile vs r ≠ 0 := hv.2
          simp only [execute, hz, ↓reduceIte, effectFile, readFile_decr vs hlen]
        | true =>
          simp only [instructionOutcome, ne_eq, not_true_eq_false, ↓reduceIte,
            Option.some.injEq, Prod.mk.injEq] at hi
          rcases hi with ⟨rfl,rfl⟩
          have hz : readFile vs r = 0 := hv.2
          simp only [execute, hz, ↓reduceIte, effectFile]
      · simp [instructionOutcome, hp] at hi

#print axioms instructionOutcome_sound
end M6.Source

