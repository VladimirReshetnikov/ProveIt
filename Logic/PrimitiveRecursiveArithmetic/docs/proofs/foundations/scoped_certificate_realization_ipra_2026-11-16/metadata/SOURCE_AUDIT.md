# Source audit

## Repository pin

- Repository: `https://github.com/VladimirReshetnikov/ProveIt`
- Branch inspected: `main`
- Final pin: `f444b76e8480ebea128c15b4a59f158e14f478cc`
- Commit date: 2026-11-16 19:44:47 UTC
- Commit message: `New research report(s)`
- The commit itself adds a Bring/quintic incoming packet; the ordinary iPRA
  core and framework files audited below were already present in its parent.

The branch advanced during the audit from
`99221756b5c5f597c2b893863f5ec21b86c7ee11`; the report was repinned to the
later commit before packaging.

## Canonical object theory and logic

- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
  - `PR`, `PTm`, `PRAAx`, `PRA.qfInd`.
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Syntax.lean`
  - scoped syntax, shifts, substitutions, `Fm`, `Fm.QF`.
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean`
  - `Prf`, intuitionistic natural deduction, `Prf.subst`, `Prf.weaken`,
    `Prf.trans`, `Prf.exE`.
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`
  - blob `ccfe499b9687ea0e176f832686d8e492fe15544b` at the pin;
  - `native_iff_pra`, `pra_iff_native`, round trips, equiconsistency.
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeClausalDiagonal.lean`
  - `KPrf`, checked substitution, cut, and export to `NPrf`.

## Checked arithmetic library

- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core/Basic.lean`
  - open induction and arithmetic instantiation.
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core/Search.lean`
  - `Search.mu`, `search_spec`, `search_found`, `search_minimal`.
- `Logic/PrimitiveRecursiveArithmetic/Derivations/README.md`
  - module inventory and axiom-audit policy.

## Bridge

- `Logic/PrimitiveRecursiveArithmetic/Bridge/Lean/IPRABridge/FoundationToConcise.lean`
  - blob `9d32af8e49685e18588a5bad63514728dc54f649`;
  - `hilbertToConcise` is uniform in free-term assignments;
  - the public theory wrapper is closed.
- `Logic/PrimitiveRecursiveArithmetic/Bridge/Lean/IPRABridge/ConciseToFoundation.lean`
  - blob `d7e9fd4af8dc30376e03f0facbfe08b7de78d241`;
  - `toFoundation_provable_of_axioms` already transports open finite contexts
    under arbitrary environments.
- `Logic/PrimitiveRecursiveArithmetic/Bridge/README.md`
  - documents the current closed APIs and round-trip caveat.

## Packet catalogue and prior frameworks

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/UNIFICATION-PLAN.md`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`
- `.../foundations/ipra_embedding_framework/README.md`
- `.../foundations/ipra_finite_query_normal_form_2026-11-16/README.md`
- `.../foundations/ipra_finite_query_normal_form_2026-11-16/metadata/DIFFICULTY_MATRIX.csv`
  - blob `a4ce3c68be820385f25b3c08015b2dc15cbab540`.
- `.../foundations/ipra_cbip_framework_2026-11-16/README.md`
- `.../foundations/ipra_native_clause_framework_2026-11-15/README.md`
- `.../foundations/ipra_native_clause_framework_2026-11-15/metadata/DIFFICULTY_MATRIX.csv`
  - blob `1d2a8109f19ab0f59010b179481cf9b58513f815`.

## Audit interpretation

The repository itself distinguishes checked core/derivation/bridge files from
filed proof packets that were not rerun or compiled during placement. This
archive follows that distinction. Existing declaration names are cited as
upstream checked; new Lean declarations are marked candidate or blueprint.
