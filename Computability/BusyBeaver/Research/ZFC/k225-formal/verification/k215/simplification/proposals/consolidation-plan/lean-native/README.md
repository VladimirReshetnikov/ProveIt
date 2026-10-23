# Native Replacement after quotient collection

This is a checked implementation of the existing `collection-first` and
`native-replacement` research proposals against ProveIt commit
`cbf94cb552a3b49509e0eee80e7455d4eb5974c6`. It changes no machine, numerical
calculus, or public consistency statement.

## Mathematical change

`KQ1Collect.quotient_collection` already transports every actual first-order
formula to the quotient with native equality. The new module derives Replacement
there by one guarded functional-image lemma. It avoids the additional
raw-representative, bisimilarity-invariance, and quotient-descent argument in the
active proof of Replacement.

The guard is essential. Apply collection to the actual formula
`Mem(0,2) ∧ rename guardRename phi`, where `guardRename` sends slots
`0 → 1`, `1 → 0`, and `k+2 → k+3`. Under the environment `(x,y,a,env)`, this
formula says `x ∈ a ∧ phi(y,x,env)`. Collection gives a supported output set and
one witness for each input that has an output. Functionality makes that witness
equal to any requested output, proving exact image membership. No totality or
collection for arbitrary semantic predicates is assumed.

## Necessary import change

Replacing only the direct `KQ1ZF` reference increases the active closure: the old
Replacement development is still imported through
`InductiveAttempts → QuotientReplacement → KQ1Replacement`.

The final patch separates `InductiveAttemptsCore` (the unchanged generic proof)
from the original `InductiveAttempts` facade (the unchanged CP/GIC
specializations). `KQ1ZF` imports the core and the new native Replacement module.
The old module names and all old declarations remain available. The source-split
audit verifies that the generic and specialization proof bodies are unchanged.

## Exact measurements

Physical source/import census of the literal `KEndpoint215` closure:

| Metric | Current commit | Proposed overlay | Difference |
| --- | ---: | ---: | ---: |
| Project modules | 174 | 173 | -1 |
| UTF-8 source bytes | 1,752,650 | 1,744,292 | -8,358 |
| Physical source lines | 37,648 | 37,483 | -165 |

These are static dependency measurements, not proof-object sizes or measured
build speedups. Preserving compatibility adds **3,902 bytes and 84 physical
lines** across all maintained affected sources. The result simplifies the
active endpoint; it is not a repository-wide source deletion.

## Verification performed

Lean **4.32.0** freshly compiled **107 project modules and two audit clients**
in `build02`, with no imported project objects reused from an earlier build.
The compilation includes the changed lower chain and the unchanged generic
`KEndpoint.blank_halts_iff_zfc_refutation`, plus the old Replacement and
InductiveAttempts interfaces. The 109 compiler processes took 55.58655 seconds
in total in this environment; this is not a comparative benchmark.

The audit clients emitted no warnings or errors. Existing dependency modules
emitted 15 warnings. No `sorryAx` occurred. Assumption reports:

| Declaration | Reported assumptions |
| --- | --- |
| `exact_image` | none |
| `sat_guardForm`, `replacement_of_collection` | `propext` |
| New and old quotient Replacement endpoints | `propext`, `Classical.choice`, `Quot.sound` |
| `KQ1ZF.zf_consistent`, generic `KEndpoint` | `propext`, `Classical.choice`, `Quot.sound` |

Typed clients check both new endpoint signatures and equality with the old
proofs by proof irrelevance; this equality checks the exact theorem type, not
equality of algorithms or proof-processing cost. The old nine-declaration
Replacement interface is also checked. `git apply --check` succeeds.

**Not performed:** compilation of the literal `KEndpoint215` source, boot, and
site certificates under this overlay. Existing historical machine receipts do
not certify a new full-machine build. That remains the integration gate.

## Files and replay

- `overlay/`: four replacement/new production source files, preserving module paths.
- `audits/`: exact endpoint and legacy compatibility clients.
- `native-replacement.patch`: repository-relative patch; no repository is modified by replay.
- `replay.py`: fresh serial component build, with exact commit and compiler checks.
- `closure-census.json`: source hashes, imports, and counts for both literal endpoint closures.
- `split-audit.json`: preservation checks for the source split.
- `build02/receipt.json`, `build02/logs/`, `build02/sources/`: final successful evidence.
  Compiled objects are disposable and need not be distributed.

```sh
python3 replay.py \
  --repo /absolute/path/to/ProveIt \
  --lean /absolute/path/to/lean-4.32.0/bin/lean \
  --build /absolute/path/to/new-empty-build
```

The driver uses a shared advisory proof-build lock. It requires materialized
project import sources from the pinned checkout, but neither a prebuilt project
cache nor Mathlib. The final 109-module check uses only the official Lean
toolchain and those project sources.

## Attribution

The elementary guarded-image argument and the proposed native Replacement
route already appear in the repository's `collection-first` and
`native-replacement` packets. This contribution is the current-source adapter,
minimal import split, exact compatibility checks, measured closure change, and
fresh component compilation. The finite-attempt proof and all unchanged
dependencies remain the original repository work and retain their attribution.
