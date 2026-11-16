# Formalization status

| Artifact | Status |
|---|---|
| `FiniteContractSemantic.lean` | Semantic prototype; uncompiled; nontrivial proofs explicitly contain `sorry`. |
| `ObjectCompilerBlueprint.lean` | Uses actual ProveIt imports and types; uncompiled; several final encoded formulas remain schematic. |
| Human finite-trace proof | Complete in the report. |
| Human contract-DAG proof | Complete in the report. |
| Human relational finite-horizon proof | Complete in the report. |
| Human cubic proof | Complete in the report and checked by exact Python tests. |
| Generic `Prf PRAAx` trace theorem | Not implemented. |
| Generic `Prf PRAAx` DAG compiler | Not implemented. |
| Native-core export | Existing bridge identified; no export claimed without the missing object theorem. |

The archive intentionally distinguishes theorem statements, semantic Lean
proof targets, and deeply embedded iPRA derivations.
