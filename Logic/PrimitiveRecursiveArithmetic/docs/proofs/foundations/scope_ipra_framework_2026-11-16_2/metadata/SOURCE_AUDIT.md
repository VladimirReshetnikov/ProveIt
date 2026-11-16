# Source audit

Pinned repository: `VladimirReshetnikov/ProveIt`

Pinned revision: `8dfe26af18310f58aaff695fb0ce03ff5007d096`

Audit date: 2026-11-16

Primary paths reviewed:

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/UNIFICATION-PLAN.md`
- `Logic/PrimitiveRecursiveArithmetic/ENDPOINTS.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core/Basic.lean`
- `.../Core/Definitions.lean`
- `.../Core/Order.lean`
- `.../Core/Pairing.lean`
- `.../Core/Search.lean`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`
- `.../foundations/FINER-iPRA-framework-2026-11-16/`
- `.../foundations/scoped_certificate_realization_ipra_2026-11-16/`
- `.../foundations/ipra_bounded_reflection_2026-11-16/`

Key API facts used:

- `Prf.subst`, `Prf.weaken`, `Prf.trans`, `Prf.exE`, `Prf.impI`, `Prf.ofNil`;
- `PRA.qfInd`, `LeanProofs.IPRA.ind`, `LeanProofs.IPRA.inst`;
- `PTm.toPR`, `toPR_eq`, `recDef`;
- `Search.mu`, `search_spec`, `search_found`, `search_minimal`;
- equality bit `eqb`, quantifier-free `le` and `lt`.

The local artifact environment did not contain Lean, and network access from the
container was disabled. Repository sources were inspected through the GitHub
connector; the Lean files in this archive must be re-audited and elaborated in
the pinned or a later compatible checkout.
