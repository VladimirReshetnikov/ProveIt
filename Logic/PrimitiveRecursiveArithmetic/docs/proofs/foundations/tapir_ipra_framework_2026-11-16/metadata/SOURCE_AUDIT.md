# Source audit

## Repository pin

- Repository: `VladimirReshetnikov/ProveIt`
- Branch: `main`
- Commit: `58627ed89814ba122e1f0f012f1aba103cda267b`
- Commit date observed: 2026-11-16 20:33:53 UTC
- Commit message observed: `Place the Lambert W iPRA packet under docs/proofs/analysis`

## Canonical object theory

Inspected at the pin:

- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean`
  - `Prf`, scoped natural deduction, `Prf.substWeaken`, `Prf.weaken`,
    `Prf.subst`, `Prf.trans`, `Prf.exE`.
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
  - `PR`, `PTm`, `PRAAx`, `PRA.qfInd`.
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeClausalDiagonal.lean`
  - `KPrf`, substitution, cut, and export to the native kernel.

## Checked arithmetic and framework dependencies

- `Derivations/Lean/IPRADerivations/Core/Basic.lean`
  - arithmetic symbols, `IPRA.inst`, open `IPRA.ind`.
- `Derivations/Lean/IPRADerivations/Core/Definitions.lean`
  - `PTm.toPR`, `recDef`, recursion equations, bounded sums/products.
- `Derivations/Lean/IPRADerivations/Core/Search.lean`
  - least search, `search_spec`, `search_found`, `search_minimal`.
- `Derivations/Lean/IPRADerivations/Core/Pairing.lean`
  - equality bit, pairing/projections, simultaneous recursion.
- `Derivations/Lean/IPRADerivations/Foundations/BoundedReflection.lean`
  - bounded universal/existential bits, reflection, decidability, least witness,
    `bounded_choice`.
- `Derivations/Lean/IPRADerivations/Foundations/Termination.lean`
  - measure-decreasing stopped-run termination.

## Repository-level status documents

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ENDPOINTS.md`
- `Logic/PrimitiveRecursiveArithmetic/UNIFICATION-PLAN.md`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`

The current repository distinguishes checked core/derivation modules from
research packets that may contain human proofs, tests, or Lean blueprints but
no constructed `Prf PRAAx` for their main theorem.  This archive preserves that
distinction.

## Prior framework baselines

The design was compared with:

- `FINER-iPRA-framework-2026-11-16` (finite interaction normal form with
  explicit residuals);
- `scoped_certificate_realization_ipra_2026-11-16` (certificate escape
  analysis);
- finite-query, native-clause, bounded-reflection, and unified finitary
  framework packets catalogued under `docs/proofs/foundations/`.

TAPIR does not repeat their semantic frameworks.  It targets the remaining
last-mile compiler into ordinary `Prf PRAAx`, and updates older difficulty
claims to account for the now-checked bounded-reflection module and current
open-sequent bridge status.
