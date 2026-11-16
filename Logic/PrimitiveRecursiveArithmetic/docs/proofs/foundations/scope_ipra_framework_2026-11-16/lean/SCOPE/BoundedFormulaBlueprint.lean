import IPRADerivations.Core.Search
import IPRADerivations.Core.Pairing
import IPRADerivations.Core.Definitions

/-!
# Fixed bounded-formula reflection: implementation blueprint

This file gives the intended source definitions and theorem signatures for the
SCOPE bounded-formula compiler.  It is an outline, not a kernel-checked module.
No unproved declaration is introduced: unfinished theorem signatures appear
inside comments.

Important current APIs used here:

* `PTm.toPR` and `toPR_eq` remove the older arity-abstraction obstacle;
* `recDef`, `rec_zero`, and `rec_succ` build arbitrary-arity finite folds;
* `eqb`, `eqb_of_eq`, and `eqb_of_ne` reflect equality;
* `Search.mu`, `search_spec`, `search_found`, and `search_minimal` provide the
  least bounded witness with a failure sentinel;
* `Prf.subst` plus `Syn.up` and `Fm.subst_inst` handle binder-aware
  specialization of the resulting derivations.
-/

namespace LeanProofs.IPRA.SCOPE.Bounded

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus)

/-- Fixed bounded formulas.  In `allLt` and `exLt`, de Bruijn variable `0` of
`body` is the bounded variable; `bound` lives outside the binder. -/
inductive BForm : (n : ℕ) → Type
  | eq {n : ℕ} (s t : PTm n) : BForm n
  | bot {n : ℕ} : BForm n
  | and {n : ℕ} (A B : BForm n) : BForm n
  | or {n : ℕ} (A B : BForm n) : BForm n
  | imp {n : ℕ} (A B : BForm n) : BForm n
  | allLt {n : ℕ} (bound : PTm n) (body : BForm (n + 1)) : BForm n
  | exLt {n : ℕ} (bound : PTm n) (body : BForm (n + 1)) : BForm n

/-- Boolean negation, valid on proved bits. -/
def bnot {n : ℕ} (a : PTm n) : PTm n := monus (num 1) a
/-- Boolean conjunction, valid on proved bits. -/
def band {n : ℕ} (a b : PTm n) : PTm n := a * b
/-- Boolean disjunction, valid on proved bits. -/
def bor {n : ℕ} (a b : PTm n) : PTm n :=
  bnot (band (bnot a) (bnot b))
/-- Boolean implication, valid because every compiled antecedent is decidable. -/
def bimp {n : ℕ} (a b : PTm n) : PTm n := bor (bnot a) b

/-- Move a body with variables `[i, x_0, ..., x_(n-1)]` into a recursion step
with variables `[i, accumulator, x_0, ..., x_(n-1)]`. -/
def liftFoldBody {n : ℕ} (body : PTm (n + 1)) : PTm (n + 2) :=
  Syn.subst (Fin.cases (var 0) (fun j => var j.succ.succ)) body

/-- Product fold over a Boolean body.  The recursion argument is first. -/
def allFoldPR {n : ℕ} (body : PTm (n + 1)) : PR (n + 1) :=
  recDef (num 1) (band (var 1) (liftFoldBody body))

/-- Disjunction fold over a Boolean body. -/
def exFoldPR {n : ℕ} (body : PTm (n + 1)) : PR (n + 1) :=
  recDef (num 0) (bor (var 1) (liftFoldBody body))

/-- Apply an `(n+1)`-ary fold to a bound and the current `n` parameters. -/
def foldAt {n : ℕ} (f : PR (n + 1)) (bound : PTm n) : PTm n :=
  app f (Fin.cases bound (fun i => var i))

/-- Object-language meaning of a bounded formula. -/
def denote : {n : ℕ} → BForm n → Fm PTm n
  | _, .eq s t => s ≐ t
  | _, .bot => Fm.bot
  | _, .and A B => denote A ⋏ denote B
  | _, .or A B => denote A ⋎ denote B
  | _, .imp A B => denote A ⟶ denote B
  | _, .allLt bound body =>
      Fm.all (LeanProofs.IPRA.lt (var 0) (Syn.shift bound) ⟶ denote body)
  | _, .exLt bound body =>
      Fm.ex (LeanProofs.IPRA.lt (var 0) (Syn.shift bound) ⋏ denote body)

/-- The compiled characteristic term. -/
def bit : {n : ℕ} → BForm n → PTm n
  | _, .eq s t => eqb s t
  | _, .bot => num 0
  | _, .and A B => band (bit A) (bit B)
  | _, .or A B => bor (bit A) (bit B)
  | _, .imp A B => bimp (bit A) (bit B)
  | _, .allLt bound body => foldAt (allFoldPR (bit body)) bound
  | _, .exLt bound body => foldAt (exFoldPR (bit body)) bound

/-- Package returned by the meta-level compiler. -/
structure Reflection {n : ℕ} (A : Fm PTm n) where
  bit : PTm n
  boolean : ([] : List (Fm PTm n)) ⊢[PRAAx]
    ((bit ≐ num 0) ⋎ (bit ≐ num 1))
  forward : ([] : List (Fm PTm n)) ⊢[PRAAx]
    (A ⟶ (bit ≐ num 1))
  backward : ([] : List (Fm PTm n)) ⊢[PRAAx]
    ((bit ≐ num 1) ⟶ A)

/-!
The implementation should prove, in this order, the following declarations.
They are comments so this blueprint introduces no unchecked theorem.

```
theorem bnot_boolean ...
theorem band_boolean ...
theorem bor_boolean ...
theorem bimp_boolean ...

theorem allFold_zero ...
theorem allFold_succ ...
theorem exFold_zero ...
theorem exFold_succ ...

-- Pointwise reflection of the finite folds.  The invariant is an equation
-- about the fold bit plus a free candidate index, hence quantifier-free.
theorem allFold_at {body : PTm (n+1)} {N i : PTm n} ...
theorem allFold_counterexample {body : PTm (n+1)} {N : PTm n} ...
theorem exFold_witness {body : PTm (n+1)} {N : PTm n} ...
theorem exFold_of_witness {body : PTm (n+1)} {N i : PTm n} ...

-- Main schema, by structural recursion on the fixed syntax tree.
def reflect (A : BForm n) : Reflection (denote A)

-- No bespoke binder rewrite is needed to instantiate the theorem: use
-- `(reflect A).forward.subst sigma` and `(reflect A).backward.subst sigma`.
-- A separate compiler-coherence theorem is desirable for generated code.
theorem bit_subst_ext (A : BForm n) (sigma : Fin n -> PTm m) :
  ([] : List (Fm PTm m)) ⊢[PRAAx]
    (Syn.subst sigma (bit A) = bit (BForm.subst sigma A))
```

For the bounded existential case, compile the body bit `b(i,x)` and apply the
checked `Search.mu` to the zero test of `1-b`.  `search_found` supplies a
witness, `search_minimal` supplies leastness, and the sentinel value is the
bound.  For the bounded universal case, search for a counterexample to the
body bit.  This avoids induction on a formula containing an object quantifier.
-/

end LeanProofs.IPRA.SCOPE.Bounded
