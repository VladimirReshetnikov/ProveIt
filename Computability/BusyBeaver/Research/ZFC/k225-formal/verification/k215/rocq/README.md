# Rocq K215 build

The [later compact-certificate check](../simplification/phase2/rho8-global/rocq/README.md)
rebuilds all seven affected modules and obtains four closed endpoint reports.
Its 735-instruction rendering has 22,673 bytes, and a focused recursive check of
the changed dominated-rule module passes. This incremental result preserves the
original full-build and recursive endpoint receipts below.

**Status: `PASS_CLOSED_KERNEL`** (2026-10-21). All 237 modules compiled with
Rocq 9.1.0, OCaml 4.14.2 and rocq-stdlib 9.0.0. The matching `coqchk` recursively
rechecked `K215F.CorrectDense215` with no `-admit` or `-norec` option.

These are the original full-build receipts at `613f9cf28a`. The
[subsequent compact-proof check](../simplification/rocq/README.md) recompiles all
seven affected modules, reruns the four closed endpoint reports, and recursively
checks the changed dominated-rule module against the preserved baseline. It
does not claim a second full 237-module replay.

The sparse and dense endpoints each printed exactly two
`Closed under the global context` reports and no `Axioms:` report. Their final
statements establish halting iff `StandardZFC ⊢TC ⊥`, and nonhalting iff its
negation, for the exact 215-state dense table. The dense table SHA-256 is
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`;
the source SHA-256 is
`17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`.
Separate Python runtime checks are not premises of these proofs.

- [Original source/object/log audit](actual/actual-review.json): all 237 baseline sources,
  exact snapshots, imported objects, compiler commands and output logs agree.
- Raw endpoint reports: [sparse](actual/K215F.Correct215.log),
  [dense](actual/K215F.CorrectDense215.log).
- [Recursive kernel log](actual/coqchk.log).
- [Complete evidence archive](actual/evidence.tar.gz) and
  [member index](actual/evidence-index.json): exact executed driver, all module
  records and source snapshots, logs, toolchain history, failed/interrupted attempts,
  generator checks, and portable-driver review/control history. Compiled objects
  are recorded by hash rather than bundled.
- [Saved-record audit](actual/saved-review.json), produced by
  [review_saved.py](review_saved.py). This checks the archived evidence without
  invoking a compiler or claiming a new check of the live `.vo` objects.

The successful module compilations took 2,225.787 seconds in total; recursive
`coqchk` took 1,648.988 seconds. These are proof-process times, excluding installation,
lock waits and the preserved interrupted performance attempt.

The global `coqchk -o` context lists `BusyCoq.LibTactics.inj_pair2`,
`Stdlib.Logic.ProofIrrelevance.proof_irrelevance` and
`Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq`. The four endpoint statements depend on
none of them, as the closed dependency reports show. The global report lists no
constants relying on type-in-type, unsafe (co)fixpoints, or assumed positivity.
This is an endpoint-dependency claim, not a claim that every imported library
contains no axioms.

## Reproduction

The [portable driver](build.py) builds the complete target closure from source:
42 K215 modules and 195 selected pinned reference modules. The dependency sources
are K230 commit `3142e4dd980f0be12f4abb636c4ae2528afc17eb` and Jeff's reference
commit `c132d7eae8158cd3a9850ea3eb7251158c3dd821`. No previously compiled K230
endpoint is needed. See the [toolchain and command-line instructions](../../../rocq/rocq-extension/README.md#the-215-build-route).
Each proof invocation takes the shared Lean/Rocq lock.

The actual build ran with the preserved private-workspace runner. The portable
successor has configurable checkout/output paths and stronger resume and signal
cleanup gates. It passed an exact 237-module source/dependency-plan comparison and
eight controls using fake files and disposable Python children. This validation
is not a second proof compilation. Its independent
[source review](../independent-audit/portable-rocq-v3/review.json) preserves the
findings and correction history. The final live audit independently checked the
actual raw endpoint reports, rather than relying on the older runner's resume gate.

To check the published records without any proof compilation, run from this directory:

```sh
python3 -B review_saved.py --evidence actual --output /tmp/k215-rocq-saved-review.json
```

## Repairs and retained history

No theorem statement or axiom was weakened or added.

- Three `Sim230` tactic case splits used the old bound 40 although the checked
  paths and theorem bound were already 48. The splits and generator were aligned.
- `DomRho8` makes `wim` locally opaque after its arithmetic-bound and zero-alias
  lemmas. The transparent attempt was deliberately interrupted after 191.241 seconds
  for performance; the same generated certificate then compiled in 8.174 seconds.
  This was not a logical proof failure.
- All 42 generated proof sources reproduce exactly. The source/generator/documentation
  manifest entries were updated. One pre-existing variant-229 JSON pin was aligned
  with committed LF bytes, preserving the original upstream CRLF pin and parsed-source
  equality observation. That input was not rewritten. The final metadata change
  preserves the original formatting and replaces only five manifest hashes and
  two regeneration hashes; the [successor receipt](actual/metadata-format-correction.json)
  records the correction. The reindented intermediate remains in the unchanged
  evidence archive and [separate history](history/metadata-format-v1/metadata-finalization.json).
- Toolchain setup interruptions and the setup-only first driver failure are kept
  separately from project compilation. The current successful dependency objects
  were built fresh from the pinned sources, then reused only across this build's
  recorded attempts.
