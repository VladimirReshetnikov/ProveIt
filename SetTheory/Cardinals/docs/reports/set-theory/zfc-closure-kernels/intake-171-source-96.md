# Batch 171, Source 96: Shifted_Pairing_Companion_Sources_2026-10-18

**Imported in `950e2f0ff6`; incoming ZIP retired.** Arrival `4c3571540cc01f681049cd03f9385351c450ac95`. Author snapshot: `fd1adfa19f8fe8da41444e3fa43b89a59d891067 (native-model adapter comparison); original Dag254 binding recorded in INPUTS.json`. This is an addition to the existing reconciliation host, not a new machine record.

These are intake findings from manuscript and source review. Numerical details in the contribution section retain the delivered scope; the execution section below identifies fresh checks separately. The complete original manuscript and dependencies can be restored using [the recovery instructions](intake-171-reproduction.md).

## Retained results and arguments

- Full dirty-scratch contracts for E(a,b)=2^a(2b+1)-1 and its inverse, with complete clean-call fixed-point evidence distinguishing external helper entry from internal backedges.
- Generic pairing/native-theory transfer addresses a formula code also used as its own bound-variable label. Explicit example old R(1,1)=17 versus shifted21 refutes naive gate transport. The proof handles actual finite native matrices, equality, parameters, truth alias0, and a=b empty-image case.
- Matched whole-source costs and bounded 200-shape search: direct234/best232 DAG nodes versus219 baseline; dirty-contract and independent CFG tests.

## Overlap and superseded claims

- The shifted pairing formula and eight-register application already appear in maintained register_lifetime.md. This archive adds a different direct-helper implementation, generalized dirty contracts and detailed own-code native calibration; do not present the formula itself as newly discovered.
- Unshifted 2-adic compiler costs in compiler_route.md are distinct and do not prove this shifted transfer.

## Limits, corrections and open work

- 232 is a source-DAG count, not a physical-state count. No table, blank bootstrap, or binary runtime is supplied.
- The native comparison is ordinary mathematical transfer, not equality of old/new numerical theorem sets or a checked Lean/PA theorem.
- Main proof assumes the established native-calculus calibration and effectivity assumptions where primitive-recursive translations are claimed.

## Current repository comparison

Quoted passages and line numbers refer to review checkpoint `4b3f462453`, before this intake updated the host README.

`Computability/BusyBeaver/Research/ZFC/register_lifetime.md:85`:

```text
E(a,b) = 2^a (2b+1) - 1.
```

Maintained shifted E already known; new content must be the contracts, transfer, and independently measured direct implementation.

`Computability/BusyBeaver/Research/ZFC/register_lifetime.md:117`:


Maintained eight-register implementation differs from this direct nine-register helper port.

`Computability/BusyBeaver/Research/ZFC/compiler_route.md:69`:

```text
Naively replacing recursive Cantor pairs with 2-adic pairs makes this
```

Older unshifted pairing experiment is explicitly narrower.

## Fresh execution and provenance

| Job | Result | Seconds |
| --- | --- | ---: |
| `A16-prepare-local-archive` | PASS | 0.064 |
| `A16-prepare-inputs` | PASS | 0.115 |
| `A16-shifted-source` | PASS | 9.032 |
| `A16-shapes` | PASS | 10.736 |
| `A16-pairing-math` | PASS | 0.365 |
| `A16-independent-cfg` | PASS | 23.504 |

The [terminal record](data/intake171-fresh-replay.json) retains commands, copy-only adaptations and raw-log locations. [Replay history](data/intake171-replay-history.json.gz) preserves the actual logs and newly generated or changed files. These selected finite checks do not certify the entire mathematical argument, a complete binary machine, or a PA endpoint. No Lean or Coq compiler was run for this intake.

Optional or inherited scopes not claimed as fresh:

- No inherited vendor suite and no binary simulation exists to rerun. The four leaves are the substantive suite.

## Placement

The [exhaustive placement map](data/intake171-placement.json) is authoritative for every delivered name, unchanged target, exact alias and archive-only manuscript/PDF/README. Independently supplied proof/audit notes and substantive research READMEs are retained, including the reviewed supplements to the initial extension-based inventory. Main manuscripts and PDFs remain in committed arrival archives. Existing filenames and internal references are unchanged in content; restore the original layout before execution.
