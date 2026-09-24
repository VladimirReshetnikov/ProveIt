import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Acyclic arithmetic certificates

A schedule has natural input coordinates and signed integer intermediate values.
An operand of instruction `i` can name only an input, a fixed integer, or an
intermediate with index strictly below `i`. Checking a subtraction `out = a - b`
uses the single addition `out + b = a`. Thus every instruction requires exactly
one addition or multiplication check. Equality and domain tests are separate.
-/

namespace Diophantine.ArithmeticCertificate

inductive Operation where
  | add | sub | mul
  deriving DecidableEq

def Operation.eval : Operation → ℤ → ℤ → ℤ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-- Each branch contains exactly one addition or multiplication. -/
def Operation.Check : Operation → ℤ → ℤ → ℤ → Prop
  | .add, a, b, out => a + b = out
  | .sub, a, b, out => out + b = a
  | .mul, a, b, out => a * b = out

theorem Operation.check_iff (op : Operation) (a b out : ℤ) :
    op.Check a b out ↔ out = op.eval a b := by
  cases op with
  | add => exact eq_comm
  | sub => simp only [Operation.Check, Operation.eval]; omega
  | mul => exact eq_comm

/-- The `earlier` bound makes a forward reference or a cycle ill-typed. -/
inductive Operand (inputs earlier : ℕ) where
  | input : Fin inputs → Operand inputs earlier
  | constant : ℤ → Operand inputs earlier
  | previous : Fin earlier → Operand inputs earlier

def Operand.eval {inputs earlier : ℕ} (x : Fin inputs → ℕ) (t : Fin earlier → ℤ) :
    Operand inputs earlier → ℤ
  | .input idx => x idx
  | .constant n => n
  | .previous idx => t idx

structure Instruction (inputs earlier : ℕ) where
  operation : Operation
  left : Operand inputs earlier
  right : Operand inputs earlier

def Instruction.eval {inputs earlier : ℕ} (instruction : Instruction inputs earlier)
    (x : Fin inputs → ℕ) (t : Fin earlier → ℤ) : ℤ :=
  instruction.operation.eval (instruction.left.eval x t) (instruction.right.eval x t)

def Instruction.Check {inputs earlier : ℕ} (instruction : Instruction inputs earlier)
    (x : Fin inputs → ℕ) (t : Fin earlier → ℤ) (out : ℤ) : Prop :=
  instruction.operation.Check (instruction.left.eval x t) (instruction.right.eval x t) out

theorem Instruction.check_iff {inputs earlier : ℕ}
    (instruction : Instruction inputs earlier) (x : Fin inputs → ℕ)
    (t : Fin earlier → ℤ) (out : ℤ) :
    instruction.Check x t out ↔ out = instruction.eval x t :=
  instruction.operation.check_iff _ _ _

abbrev Schedule (inputs steps : ℕ) := (idx : Fin steps) → Instruction inputs idx.val

/-- Restrict a supplied trace to the intermediate values available at one step. -/
def before {steps : ℕ} (idx : Fin steps) (t : Fin steps → ℤ) : Fin idx.val → ℤ :=
  fun earlier => t ⟨earlier.val, earlier.isLt.trans idx.isLt⟩

def Valid {inputs steps : ℕ} (schedule : Schedule inputs steps)
    (x : Fin inputs → ℕ) (t : Fin steps → ℤ) : Prop :=
  ∀ idx, (schedule idx).Check x (before idx t) (t idx)

/-- Any two valid traces of an acyclic schedule agree at every intermediate. -/
theorem Valid.unique {inputs steps : ℕ} {schedule : Schedule inputs steps}
    {x : Fin inputs → ℕ} {s t : Fin steps → ℤ}
    (hs : Valid schedule x s) (ht : Valid schedule x t) : s = t := by
  have hentry : ∀ n, ∀ hn : n < steps, s ⟨n, hn⟩ = t ⟨n, hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn
        have hbefore : before ⟨n, hn⟩ s = before ⟨n, hn⟩ t := by
          funext earlier
          exact ih earlier.val earlier.isLt (earlier.isLt.trans hn)
        have hs' := ((schedule ⟨n, hn⟩).check_iff x _ _).mp (hs ⟨n, hn⟩)
        have ht' := ((schedule ⟨n, hn⟩).check_iff x _ _).mp (ht ⟨n, hn⟩)
        rw [hbefore] at hs'
        exact hs'.trans ht'.symm
  funext idx
  exact hentry idx.val idx.isLt

/-- Number of assignments of a specified kind in the literal schedule. -/
def operationCount {inputs steps : ℕ} (schedule : Schedule inputs steps)
    (op : Operation) : ℕ :=
  (Finset.univ.filter (fun idx => (schedule idx).operation = op)).card

/-- A subtraction assignment is verified by one addition check. -/
def additionChecks {inputs steps : ℕ} (schedule : Schedule inputs steps) : ℕ :=
  operationCount schedule .add + operationCount schedule .sub

def multiplicationChecks {inputs steps : ℕ} (schedule : Schedule inputs steps) : ℕ :=
  operationCount schedule .mul

end Diophantine.ArithmeticCertificate
