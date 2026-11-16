import Mathlib.Data.Nat.Notation

/-! Finite construction codes for the primitive-recursive function symbols.
The indexed list fixes the arity of a composition's arguments. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAFiniteFunctionCodes

mutual
inductive Code : ℕ → Type
  | zero (n : ℕ) : Code n
  | succ : Code 1
  | proj {n : ℕ} (i : Fin n) : Code n
  | comp {m n : ℕ} (f : Code m) (g : Codes n m) : Code n
  | prec {n : ℕ} (f : Code n) (g : Code (n + 2)) : Code (n + 1)
  deriving DecidableEq
inductive Codes : ℕ → ℕ → Type
  | nil (n : ℕ) : Codes n 0
  | cons {n m : ℕ} (head : Code n) (tail : Codes n m) : Codes n (m + 1)
  deriving DecidableEq
end

def pack {n : ℕ} : (m : ℕ) → (Fin m → Code n) → Codes n m
  | 0, _ => .nil n
  | m + 1, f => .cons (f 0) (pack m (fun i => f i.succ))

end DiophantineConsistency.PRAFiniteFunctionCodes

namespace DiophantineConsistency.PRATheory
open PRAFiniteFunctionCodes

/-- A positional member of a finite code list. -/
def getCode : {n m : ℕ} → Codes n m → Fin m → Code n
  | _, _, .nil _, i => Fin.elim0 i
  | _, _, .cons h t, i => Fin.cases h (getCode t) i

end DiophantineConsistency.PRATheory
