# Shared implication core: checked Rocq integration

This optional component replaces the production K215 `DomRho8.v` certificate
interpreter and replay with a representation-independent theorem plus a small
adapter to the actual numeric code language. It preserves the production
`DomImp` fields `dtruth`, `dmp`, and `drho8`, their argument declarations, and
the public `rho8_all` contract.

## What is inherited and what is integrated here

The representation-independent Rocq interface and rendering structure come
from the repository's earlier
`verification/k215/simplification/proposals/shared-proof-core/rocq_core`
packet. This component does not claim to discover that abstraction.

The six-goal, 58-step plan and its parser are the same ones used by the accompanying
Lean shared-basis patch. They are restored from ProveIt commit
`49e99c5b7cc6c2e164331961de28bad3904361fd`. This differs from the three-goal plan
at the reviewed main-branch commit
`57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.

The integration supplied here makes the two languages consume that same
six-goal graph, removes the historical Rocq core's extra derivation of S,
checks the numeric adapter against the actual production providers and
enumeration clients, and updates the producer and compilation manifest.
The renderer records and checks exact parser and plan hashes:

* Parser: `63da860d3a957010c53d783a2b8995acef3d8e3806823f24fc5833738dc1d56a`
* Plan: `4141248ed90a6813c07f274351336963acde1d82f6ea463a33e5f7d64bed8005`

The upstream license and attribution files are in the parent component directory.

## Mathematical interface

`DominatedImplication.v` has no imports. Its language supplies a binary implication
constructor, a relation `below`, reflexivity, and preservation of `below` when
either side of an implication is extended. Transitivity, a truth constant,
numeric arithmetic, injectivity, and normalization are not assumptions.

For any predicate `T`, closure under modus ponens and restricted rho8 rows
implies every unrestricted rho8 row. The same shared proof graph also derives
composition, prefixing, K, Peirce, and S. `lift_right` is the usual one-step
modus-ponens corollary of the graph's prefixing formula.

The numeric adapter proves the two growth facts from the production pairing
inequalities, then instantiates the generic theorem. The old `dtruth : T 0`
field remains in `DomImp` for client compatibility. The stronger
`rho8_all_of_restricted` theorem shows explicitly that this particular result
does not use that field. No new axiom or admitted proof is introduced.

## Integration order

The optional patch is based on the reviewed main commit after applying the
separately supplied Rocq scheduler patch. Its producer also requires the
accompanying Lean shared-basis patch's six-goal parser and plan. Apply:

1. The Lean shared-basis patch.
2. The Rocq scheduler patch from the parent directory.
3. This directory's `integration.patch`.

The first two patches affect separate paths and may be exchanged. The third
patch intentionally follows the scheduler patch because both update the same
Rocq producer and manifest. `patch_manifest.json` records the exact scheduler
patch dependency and all six changed-file hashes. These six paths do not
overlap the Lean shared-basis patch's six paths.

The patch adds `rho8cd/render_dominated_core_rocq.py`, the generic generated
module, and the `rocqperm/DomRho8.v` adapter template. It updates generated
`coq/215/DomRho8.v`, `regenerate215.py`, and `manifest.json`.

## Reproduction

With `coqc` and `coqchk` on `PATH`, use a fresh output directory:

```sh
python3 check_implication.py --repo /path/to/ProveIt --out /tmp/implication-check
```

That command checks the new implication modules against the repository's
unchanged production enumeration clients. To check their combination with
the separately supplied scheduler, run:

```sh
python3 check_implication.py --repo /path/to/ProveIt \
  --scheduler-dir .. --out /tmp/combined-rocq-check
```

The script accepts `--coqc` and `--coqchk` executable paths. The recorded
combined build used Coq 8.18.0 and explicitly changed `From Stdlib` to
`From Coq` only in disposable build copies. This is recorded, including input
and compiled-source hashes, in the receipt. The generated patch sources retain
the production Rocq import namespace. No compatibility transformation is used
when the selected compiler is not an 8.x Coq executable.

After all three patches have been applied, regenerate the core directly with:

```sh
python3 /path/to/ProveIt/Computability/BusyBeaver/Research/ZFC/k225-formal/rho8cd/render_dominated_core_rocq.py
```

The renderer refuses an unexpected parser or plan hash. Its output is an
ordinary proof term; the renderer remains outside the trusted kernel.

Replay the patched calculus producer and compare all five changed modules:

```sh
python3 check_producer.py --repo /path/to/patched/ProveIt \
  --out /tmp/producer-check
```

For read-only review, `check_producer.py` also accepts `--overlay` and
`--shared-overlay`, sourcing only unchanged templates from `--repo`.

## Evidence and scope

`checked_final/receipt.json` and its logs record the fresh combined build:
twelve modules, a typed compatibility client, and recursive `coqchk` of the
generic theorem, numeric adapter, seed equivalence, and client. The client
checks all three old record-field types, `rho8_all`, and the old seed
completeness, soundness, and equivalence signatures. Nine assumption reports
are closed under the global context.

The two K230 numeric dependencies are exact, hash-pinned production source
files preserved by the earlier checked-transport packet, not the simplified
providers in the historical shared-core experiment. All other unchanged
dependencies are taken from the reviewed production K215 lane.

`producer_check/receipt.json` records byte-identical reproduction of
`DominatedImplication`, `DomRho8`, `CandidateScheduler`, `L1_CompPerm`, and
`SeedPerm` through the patched `calculus_files` function. This is a calculus
producer check, not a full machine regeneration.

The physical-machine endpoint and the full ZFC equivalence chain were not
rebuilt. The production-designated Rocq 9.1.0 toolchain was not available in
this check; the Coq 8.18 compatibility build is stated explicitly.

## Measured source reduction

All counts include comments and provenance headers. They count each logical
source module once, rather than counting both templates and generated copies.

| Source | Lines | Bytes |
|---|---:|---:|
| Old production `DomRho8.v` | 1,169 | 22,673 |
| New generic core | 298 | 15,004 |
| New numeric adapter | 55 | 2,445 |
| New core plus adapter | 353 | 17,449 |
| Change | -816 | -5,224 |

This saves 23.0% of these proof-source bytes, including the entire new generic
core. Together with the separately measured scheduler refactoring, the three
old Rocq modules total 40,773 bytes and the five replacement modules total
39,074 bytes: a net reduction of 1,699 bytes (4.2%). The combined line count
changes from 1,579 to 864. These are source counts, not kernel proof-term size,
build-time measurements, or transition-state reductions.
