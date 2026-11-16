import KIFC.KernelCore

/-!
# Boolean reflection blueprint

The structures in this file make the intended object-theory boundary explicit.
The constructors for Boolean connectives and bounded folds are the next shared
formalization milestone.  No semantic theorem is presented as an iPRA theorem.
-/

namespace LeanProofs.KIFC

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open LeanProofs.ConciseIPRA.PTm (zero succ)

/-- The numeral one in any arity. -/
def one {n : ℕ} : PTm n := succ zero

/-- A formula together with a Boolean code and object-level reflection. -/
structure Reflected (n : ℕ) where
  formula : Fm PTm n
  code : PTm n
  range : ([] : List (Fm PTm n)) ⊢[PRAAx]
    (code ≐ zero) ⋎ (code ≐ one)
  iffOne : ([] : List (Fm PTm n)) ⊢[PRAAx]
    Fm.iff formula (code ≐ one)

/-- Interface exposed by a generated bounded universal fold.  The fold is
specialized to one fixed predicate; this is not a universal evaluator. -/
structure AllFoldInterface (n : ℕ) where
  predicate : Reflected (n + 1)
  bound : PTm n
  fold : PTm n
  reflectedFormula : Fm PTm n
  foldIff : ([] : List (Fm PTm n)) ⊢[PRAAx]
    Fm.iff reflectedFormula (fold ≐ one)

/-- Interface exposed by a generated bounded existential fold. -/
structure AnyFoldInterface (n : ℕ) where
  predicate : Reflected (n + 1)
  bound : PTm n
  fold : PTm n
  reflectedFormula : Fm PTm n
  foldIff : ([] : List (Fm PTm n)) ⊢[PRAAx]
    Fm.iff reflectedFormula (fold ≐ one)

/-!
Implementation targets:

1. define fixed PR symbols `bnot`, `band`, `bor`, numerical equality and order;
2. derive Boolean range and truth-table reflection in `Prf PRAAx`;
3. generate `allB` and `anyB` by `PR.prec` for a fixed predicate symbol;
4. prove zero/successor equations with `PRA.precZero` / `PRA.precSucc`;
5. prove fold reflection while keeping the induction matrix an equation;
6. implement a metalevel syntax-directed compiler returning `Reflected n`.
-/

end LeanProofs.KIFC
