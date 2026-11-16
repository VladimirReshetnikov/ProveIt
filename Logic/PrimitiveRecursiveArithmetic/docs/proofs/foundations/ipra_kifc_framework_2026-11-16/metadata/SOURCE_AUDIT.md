# Source audit

## Repository snapshot

Primary repository: `VladimirReshetnikov/ProveIt`

Pinned snapshot used throughout this second edition:

`7c1f2594117c15a980d24300593d625722812768`

The commit was the main-branch head observed during this task on 16 November
2026. The repository is active. A later implementation should pin this hash or
repeat the API audit against its chosen revision.

## Primary inspected paths

Logical kernel and presentations:

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`

Object-derivation library:

- `Logic/PrimitiveRecursiveArithmetic/Derivations/README.md`
- `.../Core/Basic.lean`
- `.../Core/Definitions.lean`
- `.../Core/Pairing.lean`
- `.../Core/Monus.lean`
- `.../Core/Order.lean`
- `.../Core/BoundedSums.lean`
- `.../Core/Search.lean`
- `.../Core/Quotient.lean`
- `.../Core/Integers.lean`
- `.../Core/Tactic.lean`
- `.../Core/Descent.lean`
- `.../Core/DescentEx.lean`
- `.../Checks/Axioms.lean`

Relevant foundation packet:

- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_local_global/lean/NegativeSyntax.lean`
- `.../ipra_local_global/evidence/lean_build.txt`
- `.../ipra_local_global/evidence/lean_audit.txt`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`

The report also used the current repository index and commit metadata to check
that the audited API and module names still existed at the pinned revision.

## Exact API facts used by the Lean outline

- `Prf Ax Γ φ` is the deeply embedded intuitionistic natural-deduction
  judgement.
- `Prf.subst`, weakening operations, and `Prf.trans` provide term
  substitution, context management, and derived simultaneous cut.
- `PRAAx` contains defining equations for every `PR` symbol, successor axioms,
  and induction for quantifier-free formulas.
- `PRA.qfInd` is the base object induction interface.
- `LeanProofs.IPRA.ind` packages open quantifier-free induction.
- `LeanProofs.IPRA.inst` instantiates an empty-context open derivation under
  arbitrary hypotheses.
- `LeanProofs.IPRA.Search.mu`, `search_spec`, `search_found`, and
  `search_minimal` provide checked bounded least search for zero-valued terms.
- the pairing and simultaneous-recursion modules provide a checked route for
  fixed tuples and multi-accumulator state machines.
- `ipra_ring` constructs object-level polynomial equality derivations through
  the quotient/Grothendieck-ring backend.
- `pra_iff_native` transfers an ordinary `Prf PRAAx` theorem to the native
  scalar presentation.

## Status distinction used in the report

The repository itself separates three classes of material:

1. `ConciseIPRA`, a kernel-checked presentation and bi-interpretation;
2. `Derivations`, actual object-language theorems whose public conclusions are
   embedded sequents;
3. `docs/proofs`, a much larger packet corpus explicitly indexed as research
   material, often with uncompiled outlines or conditional results.

This artifact did not run the repository's Lean toolchain. Statements that a
component is checked are inherited from the inspected source and repository
build/audit records. Every new KIFC Lean file is classified separately as a
source-complete adapter, interface-only blueprint, or placeholder-bearing
formalization target.

## Negative-translation baseline

The inspected `NegativeSyntax.lean` defines the atom-preserving translation,
proves syntax/substitution facts, and translates the source arithmetic and
excluded-middle axioms. Repository evidence records that standalone module as
compiled. The translated-formula stability theorem, recursion over full source
derivations, retained recovery, and final transfer remain formalization tasks;
they are proved at the human level in this report and exposed in
`RetainedTransferBlueprint.lean` with explicit placeholders.

## Earlier framework artifacts consolidated

The following user-library artifacts were materialized and reviewed:

- `ipra_kifc_framework_2026-11-15.zip`
- `ipra_pfig_framework_2026-11-15.zip`
- `ipra_unified_finitary_framework_2026-11-15.zip`
- `ipra_finite_use_framework_2026-11-15_v2.zip`
- `ipra_certified_finitary_framework_2026-11-15.zip`
- `ocipra_framework_2026-11-15.zip`

The second edition retains their finite-demand, relational-viability,
stable-observer, guarded-operation, finite-net, and producer/verifier ideas.
Its additions are bounded-existential normal form, a full retained-transfer
argument, checked-search reuse, and a repository-specific dependency map.

## Limitations

The central indexes, logical core, current derivation backend, representative
foundation sources, and prior general frameworks were inspected. The task did
not rebuild every theorem module or independently validate every proof packet.
Packet-specific deep statements are therefore treated as targets or explicit
producer obligations unless an actual object derivation was inspected.
