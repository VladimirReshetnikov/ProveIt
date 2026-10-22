# One shared implication proof for both Rocq calculi

Baseline: ProveIt `57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.
Reference: elliotglazer/k230-rocq `3142e4dd980f0be12f4abb636c4ae2528afc17eb`.

## Result

The replacement shares one representation-independent core between the
maintained `DomRho8.v` and `CD222.v`. The former uses ordinary numerical
domination; the latter sets the domination predicate to `True`. Both adapters
preserve the interfaces actually consumed by the maintained K215 clients.

The underlying 58-detachment derivation and generic interface are inherited
from the repository's earlier `shared-proof-core` packet. This continuation
adds a two-detachment derivation of S, replacing that packet's five-detachment
extension, and wires **both** current Rocq proof files to the common core.
The core contains 60 derivation MP applications, or 61 when the unchanged
one-MP `lift_right` theorem is counted. No minimum-proof claim is made.

| Selected proof sources | Before | After |
|---|---:|---:|
| Bytes | 45,538 | 17,647 |
| Lines | 1,399 | 371 |

The reduction is 27,891 bytes (61.25%) and 1,028 lines (73.48%). The comparison
includes both original proof developments and all three replacement modules.
It excludes producer templates, audit clients and packaging. The generated
K215 lane has 43 modules instead of 42 because the shared core is a separate
module; no claim of a reduced module count is made.

## The two-step derivation of S

Write `X = A -> (B -> C)` and `Y = (A -> B) -> (A -> C)`.
The existing shared lemmas, at the explicit instances in `basisS`, supply:

1. `(((B -> C) -> C) -> (X -> Y)) -> (((B -> C) -> Y) -> (X -> Y))`;
2. `((B -> C) -> C) -> (X -> Y)`;
3. `(B -> C) -> Y`.

Apply modus ponens to the first two, then to the result and the third. The
result is `X -> Y`, exactly S. These are existing schemas `d34`, `d57` and
`d55`, respectively; the generic proof compiles without any imported library
or added axiom.

## Checks completed

- A fresh original eight-module focused tree and a fresh replacement
  nine-module tree compiled with Coq 8.18.0.
- The **same** explicit client checks nine public statements in each tree:
  `rho8_all`, the three `DomImp` projections, K, Peirce, B, S and the unchanged
  actual `ThmDom.thmDom_iff`.
- All nine client assumption reports are closed in each tree. The six generic
  core reports are also closed. Recursive `coqchk K215F.ExactTypes` passed for
  both trees, without admission or nonrecursive flags.
- The inherited `Stdlib` namespace is changed to `Coq` for the 8.18 build.
  Text loading also normalizes CRLF to LF. Exact original inputs, both digests,
  and per-file transformation counts are retained. There are no mathematical
  compatibility changes.
- The eight-file repository integration patch passes `git apply --check`.
  Its generator, templates and manifest agree. Full K215 regeneration emits
  43 sources: **40 are byte-identical**, two are the intended replacements,
  and one is the generic core. The portable regeneration driver was itself
  executed and passed the same checks.

`verification/result.json` and its original compiler/kernel logs record the
focused builds. `verification/metrics.json` gives the byte/line comparison.
`verification/regeneration-portable.json` records generator verification.
`verification/caller-audit.json` records that no other maintained `coq/215`
module refers to the retired `cd_0` ... `cd_106` implementation nodes.

## Integration boundary

The old four public basis theorems retain their exact statement headers; the
original `DomImp` record and `rho8_all` type are preserved. The unused numbered
`cd_*` implementation lemmas and the internal `Certificate` interpreter are
retired. External consumers of those implementation names would need separate
compatibility wrappers. No current K215 proof source uses the old `cd_*` names.

**The complete K215 machine endpoint has not been rebuilt for these changes.**
Rocq 9.1.0 with rocq-stdlib 9.0.0 remains the production integration gate. The
full affected closure, original endpoint assumption reports and recursive
endpoint checker should pass before adopting the overlay. Focused Coq 8.18
receipts do not replace those production checks.

## Reproduce

From this directory, with a new output directory:

```sh
python3 verify_bundle.py
python3 check.py --compat-818 --out /tmp/k215-shared-rocq-check
python3 check_regeneration.py --repo /path/to/ProveIt \
  --reference /path/to/pinned-k230-rocq --out /tmp/k215-shared-regeneration
```

For the production checker, omit `--compat-818` and pass the explicit matching
`--coqc` and `--coqchk` paths. The compile driver serializes proof invocations
using `/tmp/proveit-k215-proof-build.lock` and refuses object-cache reuse.

The patch can be reviewed without applying it:

```sh
git -C /path/to/ProveIt apply --check /path/to/integration.patch
```

`integration-overlay` contains the exact repository-relative replacements.
`inputs` contains original focused dependencies; `candidate` contains the three
new proof modules and the common typed client. No compiled objects are shipped.
The reference sources, original machine attribution and license-scope statement
are retained. See `NOTICE.md` and `source-pins.json` for exact provenance.
