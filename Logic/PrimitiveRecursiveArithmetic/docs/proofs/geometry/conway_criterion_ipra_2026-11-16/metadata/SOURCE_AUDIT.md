# Source and repository audit

Prepared 2026-11-16 (America/Los_Angeles).

## Mathematical sources inspected

1. Doris Schattschneider, “Will It Tile? Try the Conway Criterion!”, *Mathematics Magazine* 53(4), 1980, 224–233, DOI `10.1080/0025570X.1980.11976859`; an author-hosted updated PDF was inspected.  It gives the labelled criterion and the half-turn composition mechanism.
2. Matthias Weber, *Games, Graphs, and Groups: An Introduction*, version dated 2025-10-15, Section 3.4.  Its strip proof explicitly notes that fitting at vertices needs a topology argument.  This package replaces that gap by a finite torus-chain calculation.
3. The Wikipedia “Conway criterion” page was used only to confirm the contemporary public formulation and links; the proof does not rely on Wikipedia.

## ProveIt paths inspected

Repository: `VladimirReshetnikov/ProveIt`, default branch `main`.
Latest commit observed during preparation:

```text
c6643d49ab37d30d1204c689bf7f800db1a04c7b
```

Relevant files/directories:

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/README.md`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core/LinearAlgebra.lean`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core/Pairing.lean`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/topology/jordan_ipra_constructive_2026-11-15/README.md`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/cifer_ipra_framework_2026-11-15/README.md`

The checked `Derivations` library is the intended integration target.  The filed proof packets are treated as design references, not as axioms, because the repository itself marks them as unverified unless separately promoted to `Derivations`.

No remote files were edited or committed.
