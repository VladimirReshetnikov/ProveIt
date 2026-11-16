# Source audit

Pinned repository revision:
`9df5cbdf39e6220be823f611987bd584d37711fd`.

Principal checked interfaces reviewed:

- `ConciseIPRA/Syntax.lean`
- `ConciseIPRA/Deduction.lean`
- `ConciseIPRA/PR.lean`
- `ConciseIPRA/NativeBiInterpretation.lean`

Principal research packets reviewed:

- `docs/proofs/foundations/ipra_unified_finitary_framework_2026-11-15`
- `docs/proofs/foundations/ipra_finite_demand`
- `docs/proofs/foundations/ipra_local_global`
- `docs/proofs/algebra/ipra_stable_observables`
- repository-wide status summaries in `docs/proofs/README.md`

Key status distinction preserved:

- the ordinary/native iPRA backend is checked;
- `ObjectIteration.lean` and `ObjectObservation.lean` contain compiled logical
  combinators with actual `Prf PRAAx` endpoints;
- the large generic trace/relational compiler remains integration work;
- semantic Lean files and Python tests are not treated as object-iPRA proofs;
- deep certificate producers are listed separately from their finite verifiers.
