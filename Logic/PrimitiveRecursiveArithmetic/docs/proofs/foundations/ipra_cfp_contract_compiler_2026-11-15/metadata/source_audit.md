# Source audit

Inspected read-only at ProveIt `main` commit
`b88e843c31b50dfe461bfbd0380166ca422cd3ab`.

Central paths:

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`
- `.../foundations/ipra_framework_2026-11-15/`
- `.../foundations/ipra_embedding_framework/`
- `.../foundations/ipra_evidence_framework/`
- `.../foundations/ipra_finite_observation/`
- `.../foundations/ipra_framework/`
- `.../foundations/ipra_uniform_certificates/`
- `.../foundations/ipra_embedding_framework_2026-11-15/`
- `.../algebra/puiseux_ipra/evidence/scope_obstruction.md`
- `.../geometry/euler_rodrigues_ipra/README.md`
- `.../diophantine-number-theory/faltings_ipra/README.md`
- `.../diophantine-number-theory/siegel_ipra/README.txt`

The repository's own README distinguishes the kernel-checked `ConciseIPRA`
library from 58 research packets that were filed without collective rebuild or
verification.  The present package does not upgrade the status of those
packets.  It credits their stated framework components and obstacles and
provides an integration theorem and formalization architecture.
