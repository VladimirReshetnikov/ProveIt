module
public import PA196.Arithmetic.CommandInternal
public import PA196.Arithmetic.WordMacros
@[expose] public section

namespace PA196.Arithmetic.LiteralWords
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open M6.PA.SourceCantorInternal CommandStep CommandWord
open Commands M6.Source
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem triangle_numeral (n : Nat) : triangleValue (n : V) = (Cantor.triangle n : V) := by
  induction n with
  | zero => simp [Cantor.triangle]
  | succ n ih => simp [Nat.cast_add, Nat.cast_one, triangle_succ, Cantor.triangle, ih]

theorem pair_numeral (a b : Nat) : pairValue (a : V) (b : V) = (Cantor.pair a b : V) := by
  simp only [pairValue, Cantor.pair, Nat.cast_add]
  rw [← Nat.cast_add, triangle_numeral]

theorem mp_atom_numeral (b : Nat) : (atom (.mp b) : V) = mpCode (b : V) := by
  simp [atom, mpCode, ← pair_numeral]
theorem ax_atom_numeral (c x y : Nat) :
    (atom (.ax c x y) : V) = axCode (c : V) (x : V) (y : V) := by
  simp [atom, axCode, ← pair_numeral]

noncomputable def literalValue (xs : List Nat) : V :=
  xs.foldr (fun (x : Nat) (tail : V) => (x : V) ∷ tail) 0
@[simp] theorem literal_nil : literalValue ([] : List Nat) = (0 : V) := rfl
@[simp] theorem literal_cons (x : Nat) (xs : List Nat) :
    literalValue (V := V) (x :: xs) = (x : V) ∷ literalValue (V := V) xs := rfl

theorem literal_expr (xs : List Nat) (p t d : V) :
    WordExpression.eval (WordMacros.literal xs) p t d = literalValue xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [WordMacros.literal, WordExpression.eval, Scalar.eval, ih]

theorem literal_append (xs ys : List Nat) :
    literalValue (xs ++ ys) = (VectorAppend.append (literalValue xs) (literalValue ys) : V) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem eval_pair (a b : WordExpression.Scalar) (p t d : V) :
    Scalar.eval (WordMacros.pair a b) p t d =
      pairValue (Scalar.eval a p t d) (Scalar.eval b p t d) := rfl
theorem eval_mp_atom (u : WordExpression.Scalar) (p a b : V) :
    Scalar.eval (WordMacros.mpAtom u) p a b = mpCode (Scalar.eval u p a b) := by
  simp [WordMacros.mpAtom, eval_pair, Scalar.eval, mpCode]
theorem eval_ax_atom (c x y : WordExpression.Scalar) (p a b : V) :
    Scalar.eval (WordMacros.axAtom c x y) p a b =
      axCode (Scalar.eval c p a b) (Scalar.eval x p a b) (Scalar.eval y p a b) := by
  simp [WordMacros.axAtom, eval_pair, Scalar.eval, axCode]

#print axioms pair_numeral
#print axioms ax_atom_numeral
end PA196.Arithmetic.LiteralWords
