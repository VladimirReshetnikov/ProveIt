module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCommandAXInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandLiteralInternal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualCommandStepGraph ActualCommandWordGraph
open M6.Source M6.Source.CommandAtomEncoding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Numeral calibration holds in every model, not just in standard Nat. -/
theorem triangle_numeral (n : Nat) : triangleValue (n : V)=(Cantor.triangle n : V) := by
  induction n with
  | zero => simp [Cantor.triangle]
  | succ n ih => simp [Nat.cast_add,Nat.cast_one,triangle_succ,Cantor.triangle,ih]

theorem pair_numeral (a b : Nat) : pairValue (a : V) (b : V)=(Cantor.pair a b : V) := by
  simp only [pairValue,Cantor.pair,Nat.cast_add]
  rw [← Nat.cast_add,triangle_numeral]

theorem mp_atom_numeral (b : Nat) : (atom (.mp b) : V)=mpCode (b : V) := by
  simp [atom,Enumeration.encodeCommand,mpCode,← pair_numeral]

theorem ax_atom_numeral (c x y : Nat) :
    (atom (.ax c x y) : V)=axCode (c : V) (x : V) (y : V) := by
  simp [atom,Enumeration.encodeCommand,axCode,← pair_numeral]

noncomputable def literalValue (xs : List Nat) : V := xs.foldr (fun (x : Nat) (tail : V) => (x : V) ∷ tail) 0
@[simp] theorem literal_nil : literalValue ([] : List Nat)=(0 : V) := rfl
@[simp] theorem literal_cons (x : Nat) (xs : List Nat) :
    literalValue (V := V) (x::xs)=(x : V) ∷ literalValue (V := V) xs := rfl

theorem literal_expr (xs : List Nat) (p t d : V) :
    ActualWordExpression.eval (ActualWordMacros.literal xs) p t d=literalValue xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ActualWordMacros.literal,ActualWordExpression.eval,ActualCheckExpression.eval,ih]

theorem literal_append (xs ys : List Nat) :
    literalValue (xs++ys)=(InternalTrace.HFSAppend.append (literalValue xs) (literalValue ys) : V) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem run_literal_append (xs ys : List Nat) (s : V) :
    wordValue (literalValue (xs++ys)) s=wordValue (literalValue ys) (wordValue (literalValue xs) s) := by
  rw [literal_append,word_append]

#print axioms pair_numeral
#print axioms ax_atom_numeral
#print axioms run_literal_append
end M6.PA.ActualCommandLiteralInternal
