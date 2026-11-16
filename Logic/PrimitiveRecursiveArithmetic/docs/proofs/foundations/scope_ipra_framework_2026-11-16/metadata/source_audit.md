# Repository source audit

Inspected repository: `VladimirReshetnikov/ProveIt`

Pinned main commit for this report:
`58627ed89814ba122e1f0f012f1aba103cda267b`
(2026-11-16 20:33:53 UTC).

## Checked substrate and reusable APIs

- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Syntax.lean`
  - scoped variables, `Syn.subst`, `Syn.shift`, `Syn.up`, `Syn.inst`;
  - formula substitution and binder laws;
  - `Fm.QF`.
- `.../ConciseIPRA/Deduction.lean`
  - `Prf`, natural-deduction constructors, equality substitution;
  - `Prf.subst`, `Prf.weaken`, `Prf.trans`, `Prf.ofNil`.
- `.../ConciseIPRA/PR.lean`
  - `PR`, `PTm`, `PRAAx`, primitive-recursion equations;
  - `PRA.qfInd`.
- `.../Derivations/Lean/IPRADerivations/Core/Basic.lean`
  - arithmetic symbols, open `IPRA.ind`, closed theorem instantiation.
- `.../Core/Definitions.lean`
  - `PTm.toPR`, `toPR_eq`, `recDef`, arbitrary-arity recursion, finite sums and
    products. This removes the older reported obstacle of abstracting a fixed
    open term into a PR symbol.
- `.../Core/Pairing.lean`
  - `eqb`, equality reflection, pairing/projections, simultaneous recursion.
- `.../Core/Search.lean`
  - `Search.mu`, `search_spec`, `search_found`, `search_minimal`.
- `.../Core/Division.lean`, `Core/MultiSums.lean`, and related arithmetic
  modules for mixed-radix codes and finite folds.
- `Logic/PrimitiveRecursiveArithmetic/Bridge/README.md` and bridge modules
  - closed and open transport, scoped finite sequents, round trips, and symbol
    comparisons.

## Prior framework packets synthesized rather than duplicated

- `docs/proofs/foundations/ipra_unified_finitary_framework_2026-11-15`
- `.../ipra_pfig_framework_2026-11-15`
- `.../ipra_kifcr_framework_2026-11-16`
- `.../FINER-iPRA-framework-2026-11-16`
- `.../ipra_bounded_reflection_2026-11-16`
- `.../scoped_certificate_realization_ipra_2026-11-16`

Their strongest compatible ideas are combined here: fixed-program trace
reflection, explicit residuals, capped cyclic demand closure, bounded formula
reflection, backward viability, stable observers, and certificate escape
analysis. The present contribution is a single scope-normal form and an
implementation order aligned with the current checked library.

## Important catalog warning retained

The repository's proof-packet catalog explicitly distinguishes delivered
research packets from checked `IPRADerivations` modules. SCOPE preserves that
status boundary: prose, Python tests, and unelaborated Lean source are never
reported as `Prf PRAAx` theorems.
