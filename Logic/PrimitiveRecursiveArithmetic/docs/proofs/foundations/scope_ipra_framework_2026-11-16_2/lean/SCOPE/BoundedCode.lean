import IPRADerivations.Core.Search
import IPRADerivations.Core.Pairing
import IPRADerivations.Core.Definitions

/-!
# SCOPE-iPRA: schema-first bounded reflection blueprint

The key design change from a term-first `BForm n` compiler is that every
formula is a *scheme* over formal parameters.  Compilation returns a fixed
`PR k` symbol.  Later specialization only changes that symbol's arguments, so
substitution coherence is inherited from `PTm.subst_app`; no object-level
universal evaluator and no recompilation under substitution are needed.

Definitions below are intended to elaborate after routine notation adjustment.
The complete theorem targets and proof dependencies are recorded after them.
No theorem is claimed checked in this artifact.
-/

namespace LeanProofs.IPRA.SCOPE

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

/-- An atomic formula scheme together with a fixed primitive-recursive bit and
closed object derivations of Booleanity and truth reflection. -/
structure AtomSchema (k : Nat) where
  formula : Fm PTm k
  bit : PR k
  boolean : ([] : List (Fm PTm k)) ⊢[PRAAx]
    ((app bit var ≐ zero) ⋎ (app bit var ≐ one))
  one_iff : ([] : List (Fm PTm k)) ⊢[PRAAx]
    Fm.iff (app bit var ≐ one) formula

/-- Fixed bounded syntax over `k` formal parameters.  In a bounded body,
variable `0` is the bound index and the old parameters are shifted. -/
inductive BCode : Nat → Type
  | atom {k : Nat} (a : AtomSchema k) : BCode k
  | conj {k : Nat} (a b : BCode k) : BCode k
  | disj {k : Nat} (a b : BCode k) : BCode k
  | impl {k : Nat} (a b : BCode k) : BCode k
  | neg {k : Nat} (a : BCode k) : BCode k
  | exLt {k : Nat} (bound : PTm k) (body : BCode (k + 1)) : BCode k
  | allLt {k : Nat} (bound : PTm k) (body : BCode (k + 1)) : BCode k

/-- Human-facing bounded formula denoted by a code. -/
def BCode.denote : {k : Nat} → BCode k → Fm PTm k
  | _, .atom a => a.formula
  | _, .conj a b => a.denote ⋏ b.denote
  | _, .disj a b => a.denote ⋎ b.denote
  | _, .impl a b => a.denote ⟶ b.denote
  | _, .neg a => LeanProofs.IPRA.neg a.denote
  | _, .exLt bound body =>
      Fm.ex (LeanProofs.IPRA.lt (var 0) (Syn.shift bound) ⋏ body.denote)
  | _, .allLt bound body =>
      Fm.all (LeanProofs.IPRA.lt (var 0) (Syn.shift bound) ⟶ body.denote)

/-- Instantiate the human-facing formula at arbitrary terms. -/
def BCode.denoteAt {k n : Nat} (A : BCode k) (σ : Fin k → PTm n) : Fm PTm n :=
  A.denote.subst σ

/-!
## Target declarations for the checked implementation

The implementation should add an arity-generic version of `Core.Search`:

```
namespace SearchN
  def muF (body : PTm (k + 1)) : PR (k + 1)
  def mu (body : PTm (k + 1)) (N : PTm n)
      (xs : Fin k → PTm n) : PTm n
  theorem spec_open ... : [] ⊢[PRAAx] ...
  theorem found ...
  theorem minimal ...
end SearchN
```

It is the existing least-zero construction with `k` parameters left open;
`recDef` and `PTm.toPR` already support arbitrary arity.  Its induction
invariant remains quantifier-free.

Compilation then returns a symbol, not a term:

```
def BCode.char : BCode k → PR k
```

* atoms use `AtomSchema.bit`;
* Boolean connectives use fixed bit combinators by composition;
* `exLt` searches for a zero of `1 - char body` and tests `mu < bound`;
* `allLt` searches for a zero of `char body` and tests `mu = bound`.

The main record is:

```
structure Reflection (A : BCode k) where
  char : PR k
  boolean : [] ⊢[PRAAx]
    app char var = 0 ∨ app char var = 1
  one_iff : [] ⊢[PRAAx]
    (app char var = 1) ↔ A.denote
  zero_iff : [] ⊢[PRAAx]
    (app char var = 0) ↔ ¬ A.denote
```

and the compiler target is:

```
def reflect (A : BCode k) : Reflection A
```

Because `char` is a fixed `PR k`, specialization is automatic:

```
@[simp] theorem char_subst (A : BCode k) (σ : Fin k → PTm n) :
  Syn.subst σ (app (reflect A).char var) = app (reflect A).char σ
```

The formula side follows from `Fm.subst_subst`.  Thus every reflection theorem
instantiates under arbitrary contexts via `LeanProofs.IPRA.inst`, and binder
substitution is reduced to the already checked syntax laws rather than a new
compiler theorem.
-/

end LeanProofs.IPRA.SCOPE
