# Source audit

Baseline: `VladimirReshetnikov/ProveIt@7fa3ba48e8f62e8018ed954faaa48b908217eaf1`

The following current repository resources were inspected while developing the
framework.

## Repository organization

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/UNIFICATION-PLAN.md`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/README.md`
- `Logic/PrimitiveRecursiveArithmetic/Bridge/README.md`

## Object calculus

- `ConciseIPRA/Lean/ConciseIPRA/PR.lean`
  - `PR`, `PTm`, `PRAAx`
  - `PRA.proj`, `PRA.comp`, `PRA.precZero`, `PRA.precSucc`, `PRA.qfInd`
- `ConciseIPRA/Lean/ConciseIPRA/Syntax.lean`
  - substitution, shift, binders, `Fm.QF`
- `ConciseIPRA/Lean/ConciseIPRA/Deduction.lean`
  - `Prf`, `Prf.subst`, `Prf.weaken`, `Prf.trans`, `Prf.allOpen`
- `ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`
  - `native_iff_pra`, `pra_iff_native`, round trips

## Checked derivation library

- `Derivations/Lean/IPRADerivations/Core/Basic.lean`
- `Derivations/Lean/IPRADerivations/Core/Definitions.lean`
  - `PTm.toPR`, `recDef`, `rec_zero`, `rec_succ`, finite sums/products
- `Derivations/Lean/IPRADerivations/Core/Search.lean`
  - `Search.mu`, `search_spec`, `search_found`, `search_minimal`
- `Derivations/Lean/IPRADerivations/Core/Pairing.lean`
  - `eqb`, integer square root, pairing/projections, simultaneous recursion

## Bridge

- `Bridge/Lean/IPRABridge/Syntax.lean`
  - code/term/formula translations and the exact Concise round trip
- `Bridge/Lean/IPRABridge/FoundationToConcise.lean`
  - Hilbert-to-Concise transport uniform in free assignments
- `Bridge/Lean/IPRABridge/ConciseToFoundation.lean`
  - finite-context transport under arbitrary Foundation environments
- `Bridge/Lean/IPRABridge/OrderRoundtrip.lean`
  - native-order erasure/re-embedding biconditional

## Related foundation packets

- `docs/proofs/foundations/ipra_cbip_framework_2026-11-16/`
- `docs/proofs/foundations/ipra_uniformity_framework_2026-11-15/`
- the foundations catalogue entries for finite-query, relational, contract-DAG,
  observation, and bounded-interaction frameworks

## Important audit conclusion

The checked repository already supplies the structural proof operations,
primitive recursion, arithmetic, pairing, and bounded least search needed by
PCFM. The repeated missing layer is a reusable compiled object-theory library
for QF reflection, trace packaging, finite viability, stable observation, and
residual-module assembly.
