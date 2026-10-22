# Extract the power-set interface from the PSC calibration

This is a checked, narrow continuation of the phase-twelve import cleanup at
ProveIt commit `57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.

## Finding

`WFModelCore.lean` imports the complete `PSCCalibration.lean` development solely
for the predicate `PSCCalibration.PowerSets`. The predicate is two lines:

```lean
def PowerSets (mem : V → V → Prop) : Prop :=
  ∀ a, ∃ p, ∀ y, mem y p ↔ SetTheory.Sub mem y a
```

The actual uses are the arguments of `WFModel.domain_power` and
`WFModel.domain_models_ZF`. No PSC calibration theorem is used by that file.

## Change

Move that exact definition, with its existing fully qualified name and body,
into `BusyBeaver.ZFC.PowerSets`. Both `PSCCalibration` and `WFModelCore` import
the new interface. All other declarations and proof bodies in the two existing
files are unchanged. The existing `PSCCalibration` import remains compatible.

The patch does not replace a theorem by an assumption, introduce an axiom,
change a machine table, or weaken an endpoint statement. It separates a small
semantic interface from a theorem about a different presentation of set theory.

## Exact measurements

The import census resolves project modules through the repository's actual
`lakefile.toml` source roots, including the full first-order, ZF, and bounded-ZFC
consistency sources. This matters: `FirstOrder.Completeness` is still needed by
the ZFC/Choice part of the endpoint, even though it disappears from the local
well-founded-model import branch.

| Quantity | Before | After | Change |
|---|---:|---:|---:|
| KEndpoint215 project-module import closure | 179 | 177 | -2 |
| Bytes of source files in that closure | 2,129,439 | 2,100,598 | -28,841 |
| Bytes in the edited files plus new interface | 17,181 | 17,501 | +320 |

The endpoint no longer imports `Bootstrap` (9,174 bytes), `DefinableClosure`
(11,950 bytes), or `PSCCalibration` (8,112 bytes). It gains the 400-byte
`PowerSets` module, and the `WFModelCore` import line is five bytes shorter.
The historical modules remain available for their existing clients.

These are source and dependency measurements. They are not a build-time
benchmark, a reduction in the global repository size, or a claim that fewer
foundational axioms are required.

## Verification performed

- Fresh compilation of all 29 project modules in the union of the modified
  `WFModelCore` and compatibility `PSCCalibration` dependency closures.
- Fresh compilation of `Audit.lean`, including a type-preserving call to
  `WFModel.domain_models_ZF` and a definitional-equality theorem for the moved
  predicate.
- `interface_eq` has no axioms; the existing model and calibration theorems
  report `propext`, `Classical.choice`, and `Quot.sound`.
- Exact textual checks confirm that the moved declaration and all remaining
  existing proof bodies are unchanged.
- `git apply --check integration.patch` succeeds at the pinned commit.

All checks used Lean 4.32.0. The complete `KEndpoint215` endpoint was **not**
recompiled for this extraction. Integrating maintainers should run their
standard endpoint and legacy-client checks with the changed dependency
bindings before recording a new production checkpoint.

## Reproduction

Check out the pinned commit and run from this directory:

```sh
python3 verify.py --repo /path/to/ProveIt
python3 verify.py --repo /path/to/ProveIt --lean /path/to/lean-4.32.0/bin/lean --compile
```

The first command recomputes the source census and exact-move checks. The second
also compiles isolated source copies under `verification/build`; it does not
change the input repository or require external packages. The source roots
required by the endpoint census must be present, including
`SetTheory/BoundedConsistency/Lean`.

To inspect or apply the change in a working checkout:

```sh
git apply --check /path/to/integration.patch
git apply /path/to/integration.patch
```

The delivery includes only the changed sources, patch, verification script,
audit, and recorded results. Intermediate dependency copies and compiled
objects can be regenerated and need not be retained in the archive.

## Verification artifacts

`verification/result.json` records the checked scope.
`verification/compile_records.json` binds each fresh compilation to its source
hash, imports, compiler result, and object hash.
`verification/closure_metrics.json` lists both exact endpoint import closures.
`verification/audit.log` contains the printed axiom profiles.
`source_manifest.json` binds the three edited or new sources to their before
and after hashes. `verification/logs/` retains the compiler output.
