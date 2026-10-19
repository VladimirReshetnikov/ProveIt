# Batch 171, Source 82: zfc246-contextual-reassociation-20261018

**Imported in `950e2f0ff6`; incoming ZIP retired.** Arrival `7894f5ecb46ffed4947fdd6b4502e0a4e37e5533`. Author snapshot: `8e012a51d6e7fdad4d903089536427a813009a4f`. This is an addition to the existing reconciliation host, not a new machine record.

These are intake findings from manuscript and source review. Numerical details in the contribution section retain the delivered scope; the execution section below identifies fresh checks separately. The complete original manuscript and dependencies can be restored using [the recovery instructions](intake-171-reproduction.md).

## Retained results and arguments

- General relational reassociation A;(B;C) iff (A;B);C under only no escaping Break from A and no escaping Continue from C; B unrestricted, no determinism/termination premise. Normal form and finite exit relation proof includes restart loops.
- Moving-zero local transducer deletes255 and carries a selected zero to the front, exact 4 sum(A)+4 len(A)+9 clock. Explicit header-continuation obstruction prevents upgrading it to a complete machine.
- Source-equivalent but binary-invalid old178 rotation gives exact380/378-step return discrepancy; neutral226 rotation validates the comparison method.

## Overlap and superseded claims

- Current checked RMDag loop rotation and context substitution cover concrete source edits but not this general one-sided associativity theorem.
- Historical 245/246 candidates and search counts no longer improve the frontier; the failed-context counterexample and local transducer remain useful.

## Limits, corrections and open work

- Reassociation alone does not validate physical routing or backward-peek contexts.
- Moving-zero header continuation still differs; no calibrated245 machine or smaller initializer follows.
- Bounded SAT/MILP families and finite tapes are precisely scoped search rejections, not state lower bounds.

## Current repository comparison

Quoted passages and line numbers refer to review checkpoint `4b3f462453`, before this intake updated the host README.

`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMDagLoopRotation.lean:31`:

```text
theorem old_normal {p : Prog} {n l b src dst : Nat}
```

Current theorem concerns a particular transfer-plus-one loop normal form.

`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMDagContextSubstitution.lean:13`:

```text
structure Replacement (p q : Prog) (safe : Edge → Prop) (entry : Nat) : Prop where
```

Current context replacement assumes a supplied local equivalence; it does not prove this broader associativity law.

`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SourceRotation240.lean:63`:

```text
theorem local_run_iff (R R' : RMDag.Regs) (x : RMDag.Exit) :
```

Current concrete169 rewrite remains narrower than all admissible A/B/C.

## Fresh execution and provenance

| Job | Result | Seconds |
| --- | --- | ---: |
| `A02-moving-zero` | PASS | 0.114 |
| `A02-permutation-cfg` | PASS | 0.365 |

The [terminal record](data/intake171-fresh-replay.json) retains commands, copy-only adaptations and raw-log locations. [Replay history](data/intake171-replay-history.json.gz) preserves the actual logs and newly generated or changed files. These selected finite checks do not certify the entire mathematical argument, a complete binary machine, or a PA endpoint. No Lean or Coq compiler was run for this intake.

Optional or inherited scopes not claimed as fresh:

- Root-owned adapter of verify.py may reproduce four source certificates, expected affine FAILs178/190/219, PASS226, literal counterexample, and exact bootstrap. It must bypass only manifest_check, preserve expected FAIL gates, redirect writes to a persistent copy, and avoid nested reference suites.
- Large coupled search families are optional and not needed for the semantic theorem.

## Placement

The [exhaustive placement map](data/intake171-placement.json) is authoritative for every delivered name, unchanged target, exact alias and archive-only manuscript/PDF/README. Independently supplied proof/audit notes and substantive research READMEs are retained, including the reviewed supplements to the initial extension-based inventory. Main manuscripts and PDFs remain in committed arrival archives. Existing filenames and internal references are unchanged in content; restore the original layout before execution.
