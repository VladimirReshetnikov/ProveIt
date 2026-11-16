# Source audit

## Repository snapshot

Primary repository: `VladimirReshetnikov/ProveIt`

Pinned snapshot used for the report:

`8649990597d73657bde480b6c389de7f85bc0cb0`

The repository is active. A later implementation should pin this hash or repeat
the API audit against a newer hash.

## Inspected primary files

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/README.md`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core/Basic.lean`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core/Tactic.lean`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Geometry/TriangleFormulas.lean`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Checks/Axioms.lean`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`

## Exact API facts used by the Lean outline

- `Prf Ax Γ φ` is the deeply embedded intuitionistic natural-deduction
  judgement.
- `Prf.subst`, `Prf.weaken`, and `Prf.trans` provide term substitution,
  weakening, and derived simultaneous cut.
- `PRAAx` includes defining equations, successor axioms, and quantifier-free
  induction.
- `PRA.qfInd` is the base object induction interface.
- `LeanProofs.IPRA.ind` packages open quantifier-free induction for the current
  derivation library.
- `LeanProofs.IPRA.inst` instantiates an empty-context open derivation under
  arbitrary hypotheses.
- `closeAll` universally closes open theorems.
- `ipra_ring` constructs object-level polynomial equality derivations through
  the quotient/Grothendieck-ring backend.
- `pra_iff_native` transfers an ordinary `Prf PRAAx` theorem to the native
  scalar calculus.

## Inherited checked examples

The inspected `Derivations` source contains embedded derivations for:

- the two-square identity;
- Heron's factorization;
- coordinate Heron's formula;
- coordinate law of cosines.

The inspected upstream axiom-audit file states that these use Lean's standard
metatheoretic axioms and no `sorryAx`. This artifact did not independently run
that Lean build.

## Earlier framework artifacts consolidated

The following user-library artifacts were materialized and reviewed:

- `ipra_pfig_framework_2026-11-15.zip`
- `ipra_unified_finitary_framework_2026-11-15.zip`
- `ipra_finite_use_framework_2026-11-15_v2.zip`
- `ipra_certified_finitary_framework_2026-11-15.zip`
- `ocipra_framework_2026-11-15.zip`

The present work retains their finite demand, relational viability, stable
observer, guarded operation, finite-net, and producer/verifier ideas. Its main
additional contribution is to anchor composition in a small kernel-facing
schedule and in the newly available checked algebraic derivation backend.

## Limitations of the audit

The central indexes, logical core, current derivation backend, representative
checked theorem modules, and prior general frameworks were inspected. The task
did not rebuild every proof packet or independently validate every theorem
claimed by packet prose. Packet-specific deep claims are therefore treated as
targets or conditional producer obligations unless an embedded derivation was
inspected.
