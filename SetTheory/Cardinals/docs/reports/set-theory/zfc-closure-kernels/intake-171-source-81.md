# Batch 171, Source 81: zfc-below246-research-20261018 (3)

**Imported in `950e2f0ff6`; incoming ZIP retired.** Arrival `c539ed64bfad3fa5a059bf040b06b6c91ded680e`. Author snapshot: `8cdc55ff9281b0aaba49bf74b0b225d57f12b893`. This is an addition to the existing reconciliation host, not a new machine record.

These are intake findings from manuscript and source review. Numerical details in the contribution section retain the delivered scope; the execution section below identifies fresh checks separately. The complete original manuscript and dependencies can be restored using [the recovery instructions](intake-171-reproduction.md).

## Retained results and arguments

- Arbitrary-root three-class 0/1/at-least2 abstract invariant (all N^9 starting files), not just the blank-seed trace; eliminates six guards and two particular transfer-loop occurrences. Retain the exact occurrence-sensitive phase-erasure certificate.
- Spare-free increment changes only131/0 to1R103: five-step011-to000 local cleanup and 2w+11 duration; zero/positive decrement unchanged under the admitted frame. It reduces spare growth without supplying a compatible blank initializer.
- Explicit short-scanner zero-run obstruction, colored/protected-context distinction, and complete positive250/246 controls versus rejected245 attempts.

## Overlap and superseded claims

- Old 246/250 positive control counts and failed245 frontier claims are historical; current240 ordinary machine is smaller.
- General known-zero reasoning is familiar, but the all-arbitrary-root postfixed phase certificate and occurrence-level erasure are distinct reusable evidence.

## Limits, corrections and open work

- All-root theorem starts at the program root; it does not permit arbitrary interior starts.
- DAG grows203 to207 after phase erasure despite fewer leaves/guards; no state saving follows.
- The report has inconsistent prose about the rejected rotation first register selection: sections/rotation.tex suggests the first selected register can be wrong, while sections/counterexample.tex explicitly says the initial selected physical register2 is correct and the return PC differs. Reconciliation should use the exact counterexample and retain original bytes.
- Coq .v exports are inert provenance only; no Coq execution.

## Current repository comparison

Quoted passages and line numbers refer to review checkpoint `4b3f462453`, before this intake updated the host README.

`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SourceRotation240.lean:91`:

```text
theorem program_halts_iff (R : RegisterPath.Registers) :
```

Current all-register source equivalence is for a different exact rotation, not the arbitrary-root phase-erasure transform.

`Computability/BusyBeaver/Research/ZFC/candidate-rotation240/README.md:3`:

```text
This binary, single-tape machine has **240 working states**, including
```

Current ordinary frontier supersedes the old count record.

## Fresh execution and provenance

| Job | Result | Seconds |
| --- | --- | ---: |
| `A01-phase` | PASS | 0.566 |
| `A01-erasure` | PASS | 0.415 |

The [terminal record](data/intake171-fresh-replay.json) retains commands, copy-only adaptations and raw-log locations. [Replay history](data/intake171-replay-history.json.gz) preserves the actual logs and newly generated or changed files. These selected finite checks do not certify the entire mathematical argument, a complete binary machine, or a PA endpoint. No Lean or Coq compiler was run for this intake.

Optional or inherited scopes not claimed as fresh:

- Optional new controls: check_short_scanner.py for baseline scanner8355 successes/36 failures and compiled250 all8391; check_colored_runtime.py for246 all8391 and rejected2458361/30; check_blank_prefix.py exact410735/407983. Preserve expected negative outcomes.
- Skip verify_bundle.py first three reference_rebuild/reference_macro_inductions/reference_affine jobs and rocq_source_data_export; inherited vendor suites need not be rerun. export_sources.py is Python data export, but no new Coq export is needed for intake.

## Placement

The [exhaustive placement map](data/intake171-placement.json) is authoritative for every delivered name, unchanged target, exact alias and archive-only manuscript/PDF/README. Independently supplied proof/audit notes and substantive research READMEs are retained, including the reviewed supplements to the initial extension-based inventory. Main manuscripts and PDFs remain in committed arrival archives. Existing filenames and internal references are unchanged in content; restore the original layout before execution.
