# Shorter K215 proofs through checked local contracts

Prepared for Vladimir Reshetnikov, October 22, 2026 (Pacific time).

Reviewed ProveIt commit: `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.

## Result

The report proposes two concrete next simplifications and includes checked
components for both:

1. **Lean:** realize the earlier 35-template left-frame proposal as universal
   positive whole-tape contracts, with source-path framing and all machine-specific
   premises discharged.
2. **Rocq:** reuse existing macro proofs across the exact 89-node closed footprint
   common to `dag219` and `dagPerm`.

The literal 215-state machine is unchanged. This archive does **not** replace the
production site-coverage facade or contain a newly rebuilt Con(ZFC) endpoint.

The 35-template strategy and 1,422 occurrence assignments were already proposed
in `round13-left-frame`. This delivery's new work is their checked universal
frame/source/geometry realization and concrete adapter, plus the Rocq footprint
transport and certificate. The expected 6,176-to-4,789 reduction counts expensive
execution obligations, not source leaves, measured build time, or a demonstrated
reduction of the production endpoint's source size.

## Read first

- `report.pdf`: complete mathematical and engineering report.
- `report.tex`, `runtime-contracts.tex`, `rocq-and-integration.tex`,
  `references.tex`, `validation-summary.tex`: complete LaTeX source.
- `evidence/validation.json`: concise machine-readable scope and results.
- `evidence/repository-census.json`: independently recomputed source counts.
- `proof/rocq/snapshot_audit.json`: macro-library and closed-footprint census.

## Checked Lean components

The standalone build uses **Lean 4.32.0** and no mathlib or network:

```bash
python3 proof/lean/check.py \
  --lean /absolute/path/to/lean-4.32.0-linux/bin/lean \
  --out /absolute/path/to/new-empty-lean-build
```

Its import closure contains 11 unchanged vendored upstream modules and six new
modules. The driver verifies every source hash in `proof/lean/sources.json`,
compiles from an empty output directory, checks named theorem reports, and emits
compiler logs plus a receipt. There is one expected inherited linter warning in
the unchanged `KZip`; every other selected module, including all six new ones,
has zero warnings. No admissions or additional axioms are allowed.

The final declaration is:

```lean
SetTheory.BusyBeaver.ZFC.KLeftFrame215.every_template_control_closed
```

For every member of the literal 35-template family, it proves both:

- exact positive physical execution on the complete K215 tape, for every gap,
  every prefix accepted by the existing Home scan check, and every register file
  of length at least ten;
- the exact current source break/continue operation on that prefix and suffix.

It has no remaining box, Home, table-agreement, or consistency premise. Its
printed axiom profile is `propext`, `Classical.choice`, `Quot.sound`, within the
maintained endpoint profile.

All 35 literal runtime equations, all 35 geometry checks, and all 35 source-action
checks are kernel-checked. The 444 recorded operations are **symbolic executor
operations**, not concrete machine steps. Formal counterexamples explain why
the empty-left guard and the restriction on left normalization are necessary.

### Reproduce the generated template source

```bash
python3 proof/lean/generate_templates.py \
  --templates proof/lean/data/FORMAL_TEMPLATES.json \
  --output /absolute/path/to/LeftFrameTemplates215.generated.lean
cmp proof/lean/LeftFrameTemplates215.lean \
  /absolute/path/to/LeftFrameTemplates215.generated.lean
```

The input data comes from the pinned prior proposal and already uses the formal
labels. The generator is outside the proof trust base; Lean checks its output
against the actual table. The byte-identical reproduction result is recorded in
`evidence/generator-reproduction.json`.

## Checked Rocq-compatible components

The fresh pilot was checked with **Coq 8.18.0 / OCaml 4.14.1**, followed by recursive
`coqchk`. This version is distinct from the production Rocq 9.1.0 toolchain.

```bash
python3 proof/rocq/check.py \
  --deps-root proof/rocq/deps \
  --coqc /absolute/path/to/coqc \
  --coqchk /absolute/path/to/coqchk \
  --out /absolute/path/to/new-empty-rocq-build
```

The three upstream dependencies are vendored byte-for-byte. Alternatively pass
`--repo /path/to/ProveIt` instead of `--deps-root`. Their original locations and
hashes are in `proof/rocq/deps_provenance.json`.

The driver checks five modules and recursively validates the final object.
Five named reports are closed under the global context. The concrete
`macro_run_iff` preserves all exits and the exact final register function for
every one of 53 entry nodes in a checked 89-node closed subprogram. The 58 macro
specifications using those roots can consequently reuse the old mathematical
arguments after their separate `St` record interfaces are shared or adapted.

The original successful run used the repository dependency route. The later
self-contained dependency-path adaptation did not alter any proof source or
compiler command; exact copied hashes were checked. Logs and the original
receipt are in `evidence/rocq`.

## Production integration remains

1. Bind all 1,422 exact source occurrences to the templates, retaining
   `RoutedEntry`, the complete consumed path, final primitive bit, source action,
   prefix scan premise and natural-number gap arithmetic.
2. Retain all increment/decrement/halt outcomes and the three literal control
   fallbacks.
3. Supply semantic execution evidence to the endpoint instead of trying to
   infer success of a particular fuel-limited Boolean executor.
4. Preserve source decoder totality and positive progress.
5. For Rocq, share `St`, its operations, and macro specifications before replacing
   repeated theorem bodies with transfer wrappers.
6. Rebuild affected production descendants and the exact dense endpoint under
   their pinned toolchains, then measure source, object and compiler costs.

`proposals/KEndpointPort.patch` is a small endpoint interface proposal. It applies
cleanly to the pinned source but is **uncompiled**. It adds 21 source lines, so it
is enabling work rather than an immediate size saving. The full proposed file
and an independent semantic review are included beside it.

The current checked external endpoint is about syntactic ZFC refutability.
This archive does not add an internally encoded PA/ZFC proof of that endpoint.

## Reproduce the source census

```bash
python3 code/audit_repo.py --repo /path/to/pinned/ProveIt \
  --out /absolute/path/to/census.json
python3 proof/rocq/snapshot_audit.py --help
```

The census is a read-only diagnostic, not a theorem prover. It checks source
counts and finite suffix metadata but does not certify every routed occurrence.

## Rebuild the article

With a standard TeX Live installation providing the packages in `report.tex`:

```bash
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The report was rendered and visually inspected. The archive omits compiler
objects, downloaded toolchains and LaTeX temporary files. It includes relevant
accepted logs and separately labeled development failures. `MANIFEST.sha256`
hashes every packaged file except itself.

## Attribution

See `K215-NOTICE.md` and `LICENSE`. Existing machine, interpreter, source semantics,
macro specifications, mathematical calibration and template discovery retain
their ProveIt and cited predecessor attribution. The report distinguishes work
already accepted or proposed upstream from components checked in this delivery.
