import OCiPRA.TargetInterfaces

/-!
# Compiler blueprint: exact theorem signatures and construction order

This file intentionally contains definitions and comments, not admitted proof
terms.  It records the two-backend design used in the paper.

## Backend A: native scalar equations

For a fixed equation-heavy contract node, generate `NPrf` directly from:

* `NPrf.iterZero` and `NPrf.iterSucc` for iterator equations;
* the derived native equality rules from `ConciseIPRA.NativeEq`;
* `NPrf.qIInd` for literal-equation induction;
* `NPrf.qE`, `NPrf.dICase`, and `NPrf.dE` for the two native binders.

Then transfer the generated proof with

```
  native_iff_pra.mp generatedNativeProof
```

This is a typed proof-producing compiler.  It never asks iPRA to evaluate an
arbitrary unclocked program code.

## Backend B: full iPRA bounded logic

1. Reify a bounded formula into a primitive-recursive Boolean test.
2. Generate `Prf PRAAx` proofs of the Booleanization by structural recursion.
3. Express loop invariants as equations of PR tests.
4. Close them with `PRA.qfInd`.
5. Use `Prf.exI`, `Prf.impI`, substitution, and equality transport to package
   deterministic or relational witnesses.

## Target declarations

The implementation should provide the following functions (schematically):

```
def compileNativeNode
    (node : NativeNode Γ A) : NPrf Γ A

def compileDeterministicDAG
    (dag : FixedDAG n) (local : dag.LocalObjectProofs) :
    [dag.pre] ⊢[PRAAx]
      dag.post.subst (inst (PTm.app dag.program Syn.var))

def compileClockedTrace
    (machine : FixedMachine n) (bound : PR n)
    (base step finish : machine.ObjectProofs bound) :
    [machine.pre] ⊢[PRAAx] machine.post

def compileViablePath
    (cloud : FixedCloud n) (local : cloud.ObjectProofs) :
    [cloud.pre] ⊢[PRAAx] cloud.pathPost
```

Each result type is already the desired object-language derivation.  The Lean
kernel checks the compiler by checking the recursive function and every value
it returns.  Exporting a standalone certificate is a second step: encode the
resulting proof tree and replay the existing `ProofTree.checkTree` checker.
-/

namespace LeanProofs.ConciseIPRA.OCiPRA

/-- Backend choice is metadata for the host compiler, not an object-language
truth predicate. -/
inductive Backend
  | native
  | fullPRA
  | mixed
  deriving Repr, DecidableEq

/-- The four statement classes used by the packet-conversion workflow. -/
inductive StatementClass
  | deterministic
  | boundedRelational
  | stableObservable
  | conditionalProducer
  deriving Repr, DecidableEq

end LeanProofs.ConciseIPRA.OCiPRA
