import IPRADerivations.Combinatorics.LucasIdentities

/-!
# Fibonacci and Lucas recurrences along arithmetic progressions

Packet `combinatorics/fibonacci_lucas_ipra`, equation (26). Both the index
and the common difference range over arbitrary iPRA terms. The determinant
sign `(-1)^r` is encoded by the parity bit of the common difference.
The same formulas hold at an arbitrary initial offset.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.FibonacciProgression

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Fibonacci
open LeanProofs.IPRA.Combinatorics.LucasIdentities (fib_luc_mul luc_mul)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem congrLuc {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] luc a ≐ luc b :=
  congrAdd (congrFibS h) (congrMonus (congrFibS h) (congrFib h))

/-- The Fibonacci recurrence along a progression with arbitrary offset `a`. -/
theorem fib_progression (a k r : PTm n) :
    Γ ⊢[PRAAx]
      fib (a + succ (succ k) * r) + monus one (par r) * fib (a + k * r) ≐
        luc r * fib (a + succ k * r) + par r * fib (a + k * r) := by
  have middle : Γ ⊢[PRAAx] r + (a + k * r) ≐ a + succ k * r := by
    ipra_ring
  have top : Γ ⊢[PRAAx] (r + (a + k * r)) + r ≐ a + succ (succ k) * r := by
    ipra_ring
  have left := congrAdd (congrFib top)
    (.eqRefl (monus one (par r) * fib (a + k * r)))
  have right := congrAdd
    ((congrMul (congrFib middle) (.eqRefl (luc r))).eqTrans (mul_comm _ _))
    (.eqRefl (par r * fib (a + k * r)))
  exact left.eqSymm.eqTrans ((fib_luc_mul r (a + k * r)).eqSymm.eqTrans right)

/-- The Lucas recurrence along the same arbitrary-offset progression. -/
theorem luc_progression (a k r : PTm n) :
    Γ ⊢[PRAAx]
      luc (a + succ (succ k) * r) + monus one (par r) * luc (a + k * r) ≐
        luc r * luc (a + succ k * r) + par r * luc (a + k * r) := by
  have middle : Γ ⊢[PRAAx] r + (a + k * r) ≐ a + succ k * r := by
    ipra_ring
  have top : Γ ⊢[PRAAx] (r + (a + k * r)) + r ≐ a + succ (succ k) * r := by
    ipra_ring
  have left := congrAdd (congrLuc top)
    (.eqRefl (monus one (par r) * luc (a + k * r)))
  have right := congrAdd
    ((congrMul (congrLuc middle) (.eqRefl (luc r))).eqTrans (mul_comm _ _))
    (.eqRefl (par r * luc (a + k * r)))
  exact left.eqSymm.eqTrans ((luc_mul r (a + k * r)).eqSymm.eqTrans right)

abbrev fibProgressionFormula : Fm PTm 3 :=
  fib (var 0 + succ (succ (var 1)) * var 2) +
      monus one (par (var 2)) * fib (var 0 + var 1 * var 2) ≐
    luc (var 2) * fib (var 0 + succ (var 1) * var 2) +
      par (var 2) * fib (var 0 + var 1 * var 2)

abbrev lucProgressionFormula : Fm PTm 3 :=
  luc (var 0 + succ (succ (var 1)) * var 2) +
      monus one (par (var 2)) * luc (var 0 + var 1 * var 2) ≐
    luc (var 2) * luc (var 0 + succ (var 1) * var 2) +
      par (var 2) * luc (var 0 + var 1 * var 2)

/-- Universally closed Fibonacci progression recurrence, including the offset. -/
theorem fib_progression_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 fibProgressionFormula :=
  closeUniv 3 (fib_progression _ _ _)

/-- Universally closed Lucas progression recurrence, including the offset. -/
theorem luc_progression_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 lucProgressionFormula :=
  closeUniv 3 (luc_progression _ _ _)

#print axioms fib_progression_closed
#print axioms luc_progression_closed

end LeanProofs.IPRA.Combinatorics.FibonacciProgression
