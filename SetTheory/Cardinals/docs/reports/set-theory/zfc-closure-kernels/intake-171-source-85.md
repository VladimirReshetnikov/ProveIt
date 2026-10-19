# Batch 171, Source 85: zfc-layout-circuits-20261018

**Imported in `950e2f0ff6`; incoming ZIP retired.** Arrival `f750d29f9fdb2e14b96797770e8c760c7bb36345`. Author snapshot: `8e012a51d6e7fdad4d903089536427a813009a4f`. This is an addition to the existing reconciliation host, not a new machine record.

These are intake findings from manuscript and source review. Numerical details in the contribution section retain the delivered scope; the execution section below identifies fresh checks separately. The complete original manuscript and dependencies can be restored using [the recovery instructions](intake-171-reproduction.md).

## Retained results and arguments

- A computable sufficient signed safe-start recognizer. T means derivable and F means derivable relative negation, not underivability. It handles the zero alias before recursive structure and admits certified formula stacks; unknown stays unknown.
- Transport of the full nine-register product invariant and an additional zero-test oracle valid only before the first nonempty register effect. More than merely dropping six guard cases is required:5327 historical guard-only fixtures violate other masks.
- Ranked identity-collapse certificates preserve feasible successors and rule out infinite deleted-step cycles. The concrete zero-loop removals preserve source semantics but cost253/247/254 states under the measured backend, demonstrating lost sharing.
- Five complete246-state runtime layouts, two exact blank controls, deterministic control-repair policy, explicit directed-search gates/unfinished frontier, and multiple finite mutation domains.

## Overlap and superseded claims

- General finite-leaf compiler transport overlaps contextual-reassociation; do not replace the latter general theorem with these applications. Keep the signed recognizer, full-mask oracle soundness, identity-collapse proof and scoped search evidence.

## Limits, corrections and open work

- The generic safe-root theorem is already maintained; this package contributes a recognizer and applications, not a newly discovered safe-start calibration.
- 246-state controls and finite negative searches do not improve current240. Layout235/236/237 have no supplied certified blank initializer. Source/gap fingerprints alone do not prove binary transport.
- The identity-pruning product invariant assumes T=W=H=0 and cannot silently be used with every root admitted by the broader safe-start theorem.

## Current repository comparison

Quoted passages and line numbers refer to review checkpoint `4b3f462453`, before this intake updated the host README.

`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/EnumSafeStart254.lean:121`:

```text
theorem safe_start_iff (s : St) (hs : Inv s) : HaltsFrom s ↔ C254 F :=
```

The general safe_start_iff already exists.

`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DirtyProgram254.lean:66`:

```text
theorem path_halts_iff (st : AS) (hs : Safe st) :
```

Current path_halts_iff already lifts safe dirty starts to the literal program.

`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DirtyProgram254.lean:94`:

```text
theorem six_nonformula_path_iff (N A D X Y L : Nat) :
```

Six arbitrary nonformula fields with zero formula data are already covered.

`Computability/BusyBeaver/Research/ZFC/routing245_binary.md:3`:

```text
The checked [BinaryRouting245 source](../../Lean/BusyBeaver/ZFC/BinaryRouting245.lean) proves that the literal [245-state machine](candidate-routing245/README.md), started in state 0 at head 0 on the empty binary tape, halts exactly when there is a `BProv` refutation of ZF, and exactly when there is a `BProv` refutation of the repository's ZFC axioms. Negating these equivalences gives `nonhalting_iff_zf_consistency` and `nonhalting_iff_zfc_consistency`.
```

The exact routed245 external Lean endpoint is closed; older coverage/startup-gap prose is historical.

`Computability/BusyBeaver/Research/ZFC/compensated244_binary.md:8`:

```text
The proof inside PA remains open; no unconditional nonhalting or absolute
```

The different compensated244 external endpoint is closed; PA remains separate.

`Computability/BusyBeaver/Research/ZFC/source_rotation240.md:3`:

```text
`SourceRotation240` proves that the new logical register program and `ProgramRotation244.program` halt on exactly the same initial register files. The complete source/audit pair passed with 10 named axiom probes, 13 typed callers and zero warnings. Source elaboration took 1.411 seconds and the audit 0.275 seconds in the retained run.
```

Current source240 arbitrary-register source equivalence has an actual10/13 check.

`Computability/BusyBeaver/Research/ZFC/calibrated_rotation240.md:29`:

```text
For the literal 240-state binary machine, this calibration must still be
```

Source calibration alone does not close the exact240 binary endpoint.

`Computability/BusyBeaver/Research/ZFC/rotation240_coverage.md:3`:

```text
The current Lean coverage proof is **partial: 132 of 530 subtrees have passed**.
```

The maintained coverage page currently reports132/530 subtrees, not complete coverage.

`Computability/BusyBeaver/Research/ZFC/pa_internalization.md:5`:

```text
Lean checks below. The PA equivalence for the exact 240-state binary machine
```

Exact240 PA equivalence remains open; do not import an older blanket claim that no logical progress exists.

`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-170.md:19`:

```text
The rotation and predecessor-bit technique are earlier ideas, not newly claimed general methods. In particular, the complete new 6,455-leaf source list is byte-identical to Source 74's `rotate_h` list, preserved at [the earlier source file](data/74-ret242-res-srcrot-rotate_h-sites_logical.json). Source 80 contributes the precise composition that makes another binary-state fold possible, its concrete table, and the accompanying source/local/runtime arguments. A smaller source list alone would not establish the smaller machine.
```

Current source80 rotates all four H-transfer-plus-one occurrences; it preserves source74 attribution.

## Fresh execution and provenance

| Job | Result | Seconds |
| --- | --- | ---: |
| `c-layout` | PASS | 15.497 |

The [terminal record](data/intake171-fresh-replay.json) retains commands, copy-only adaptations and raw-log locations. [Replay history](data/intake171-replay-history.json.gz) preserves the actual logs and newly generated or changed files. These selected finite checks do not certify the entire mathematical argument, a complete binary machine, or a PA endpoint. No Lean or Coq compiler was run for this intake.

## Placement

The [exhaustive placement map](data/intake171-placement.json) is authoritative for every delivered name, unchanged target, exact alias and archive-only manuscript/PDF/README. Independently supplied proof/audit notes and substantive research READMEs are retained, including the reviewed supplements to the initial extension-based inventory. Main manuscripts and PDFs remain in committed arrival archives. Existing filenames and internal references are unchanged in content; restore the original layout before execution.
