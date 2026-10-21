# Shorter proofs for K215 and CM215

Research packet for Vladimir Reshetnikov's ProveIt, 21 October 2026.

**Main result:** a reusable positive-stuttering theorem and a completed standalone Lean proof that the exact existing K215 and conditional-marker CM215 machines halt equivalently from control 0 on every binary tape and at every head position. Two exact-data pilots also reduce generated Lean and Rocq source sizes substantially. **No 214-state machine was constructed.**

Repository snapshot:

```text
b6c7087477e51c017003bd729e712c8969733223
```

Read `report.pdf` for the mathematical argument, comparison, search results, and adoption plan. Its complete editable source is `report.tex`.

## What is proved and what remains

| Deliverable | Actual validation | Remaining work |
| --- | --- | --- |
| Generic positive-stuttering theorem | Lean 4.32.0, empty axiom set; Coq 8.18.0, closed context and `coqchk` pass | Replay Coq source under repository Rocq 9.1.0 before integration there |
| Exact K215–CM215 all-tape equivalence | All 24 Lean modules pass; literal tables, 215 working states each, six changed rows | Adapter from integer-indexed tape/native labels to the repository's zipper/dense semantics; compose ZFC endpoint |
| Lean shared-tree data pilot | Exact standalone `rfl` equality for both original and shared trees | Rebuild changed project module, 16 forward-checking shards, dependent endpoint closure |
| Rocq compact-path data pilot | Whole original/compact certificate equality by reflexivity, independent `coqchk` | Full affected endpoint replay under pinned Rocq 9.1.0 |
| CM215 finite-window search | Complete specified search receipts and a successful positive control | No successful 214-state candidate; broader coordinated rewrites remain open |
| Resolved source control-flow graph | Detailed proposed interface | Generic semantics theorem and certificate checker not implemented |

The standalone CM215 endpoint depends only on `propext` and `Quot.sound`. The generic Lean transport theorem has no axioms. No `sorryAx`, admitted theorem, or `native_decide` supports the new checked endpoint. The original full Lean and Rocq ZFC endpoints were not rebuilt here.

CM215 and its six-row transformation already existed upstream. This packet contributes a simpler history-free invariant and its checked transport implementation; it does not claim authorship of that existing machine or the inherited calculus/compiler. Original license and notice files are preserved.

## Main proof idea

For deterministic partial transitions, a forward simulation already transfers halting in both directions if it preserves terminal configurations, preserves a source invariant, and uses a **strictly positive finite target block** for each source step. The configuration map can be noninjective. A short induction on target halting length supplies the reverse implication.

For CM215 the map sends old control 176 to new control 52, retaining the head and whole tape. The invariant requires:

- At 52, the cell on the left is one.
- At 176, the current cell is one or the cell on the left is zero.
- At 156, the cell on the right is one.

The third clause replaces predecessor-history reasoning by one-step induction. Ordinary transitions take one target step; the exceptional zero transitions take three. This proves the equivalence from every initial tape at control 0, so no new source calibration or 95,714-step blank-start calculation is required for the local bridge.

The native halt is 254, whereas the maintained sparse formal table halts at 230. A separate read-only audit checks all 430 parent rows under 301→102, 302→120, and 254→230. This establishes exact table agreement under renaming, not the remaining tape/run adapter theorem.

## Concrete source-size reductions

| Current module | Original bytes | Proposed bytes | Saving |
| --- | ---: | ---: | ---: |
| Lean `KSource215Data.lean` | 456,548 | 239,744 | 216,804 (47.49%) |
| Rocq `Cert215Offsets.v` | 1,499,170 | 229,933 | 1,269,237 (84.66%) |

The Lean transformation shares repeated constructor subtrees through transparent definitions. The two 4,751-leaf roots need 427 distinct nodes jointly. Every other source byte and all 2,240 certificate entries remain unchanged.

The Rocq transformation stores Boolean paths as positive binary numerals with a high sentinel bit and a transparent decoder. All paths, offsets, successor indices, entry order, and the public certificate type remain unchanged.

These are exact source-data reductions. They do not establish fewer logical obligations or faster kernel checking. No performance comparison has been run.

## File map

- `report.tex`, `report.pdf`: full research article, with pinned primary-source links.
- `cm215/`: exact native/dense table inputs, independent local and label checkers, clean generators, serial Lean build driver, 24 accepted Lean source modules, and per-module logs/receipts.
- `proof_simplification/`: Lean and Coq transport lemmas, exact reference data, source-sharing and path-compaction generators, proposed data modules, full equality audits, logs, and reproduction guide.
- `reductions/`: final bounded CM215 search, four-state positive control, disjunctive register analysis, guarded source splice, and independent mathematical/table review.
- `reference/`: pinned original endpoint, table, zipper, dense bridge, and existing proof-simplification overview.
- `PROVENANCE.json`: input hashes, toolchains, and exact scope.
- `NOTICE.md`, `LICENSE`, `cm215/inputs/licenses/`: attribution and license records.
- `SHA256SUMS`: integrity manifest for all other files.

No toolchain binaries, compiled proof objects, rejected candidate tables, or obsolete failed proof experiments are included.

## Quick reproduction

Use a writable extracted copy: drivers may replace their logs and receipts. Python scripts use the standard library. The serial Lean driver uses POSIX `resource`, so use Linux, macOS, or WSL.

### Check exact local premises and native numbering

From the archive root:

```sh
python3 cm215/check_cm215_local.py
python3 cm215/check_repository_labels.py
```

The independent local checker tests all 6,880 control/five-bit-window cases. All 6,840 invariant-admissible cases pass preservation and exact one/three-step simulation.

### Rebuild the complete standalone Lean bridge

Install Lean 4.32.0 and pass its absolute executable path:

```sh
python3 cm215/build_lean.py --lean /absolute/path/to/lean
```

The bridge needs no Mathlib or ProveIt checkout. The driver compiles all 24 modules serially and writes `cm215/lean/kernel_receipt.json`. Default limits are 768 MiB and 180 seconds per module. Accepted source and log hashes are recorded in the shipped receipt.

To regenerate the 21 table/check/facade source files, leaving the three reusable proof modules in place:

```sh
python3 cm215/generate_certificate.py --chunk-size 16
```

Generation checks the native input hashes. All 21 generated files were independently regenerated from the packaged scripts and compared byte-for-byte with the accepted sources. Generation alone is not proof checking.

### Reproduce data pilots and the Coq transport theorem

From `proof_simplification/`, with a complete Coq 8.18.0 installation including `coqchk`:

```sh
python3 check_transport_coq.py \
  --coqc /absolute/path/to/coqc --coqchk /absolute/path/to/coqchk

python3 share_trees.py --out reproduced_lean \
  --lean /absolute/path/to/lean

python3 compact_rocq_paths.py --out reproduced_coq \
  --coqc /absolute/path/to/coqc --coqchk /absolute/path/to/coqchk
```

The compiler paths should be absolute, because drivers can change their working directory or resolve an executable as a filesystem path. `proof_simplification/REPRODUCING.md` gives full commands, accepted hashes, and upstream adoption gates. Recorded checks use Coq 8.18.0; the repository's intended Rocq lane uses 9.1.0, which was not replayed here.

### Reproduce the bounded reduction search

From `reductions/`:

```sh
node local_rewrite_search.cjs marker215.native.tm cm215_search_final.json 7 97
node local_rewrite_search.cjs positive-control.tm search_positive_control.json 2 8
```

The full source-analysis commands and interpretation are in `reductions/REDUCTION_NOTES.md`. The final local search found 483 valid local rewrites among 371,090 single-row alternatives, but no state fold or complete deletion. These results apply only to the stated abstraction and diagram bounds.

### Rebuild the report

From the archive root, using a standard TeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The PDF was compiled and all pages visually inspected. Package verification and source-generation checks are recorded in `PACKET_VALIDATION.json`.

## Recommended incorporation order

1. Add the generic transport theorem to the shared machine semantics layer.
2. Complete the CM215 representation adapter, compose with the existing K215 ZFC endpoint, and run the normal endpoint assumption audit.
3. Adopt each data-compaction pilot separately in its maintained generator; rebuild its affected closure under the pinned upstream toolchain and measure actual resource effects.
4. Introduce the resolved primitive control-flow graph semantics for reassociated sources, retaining all guarded destinations and control-only transitions.
5. Search coordinated selector-test reorderings for 214 states, emitting an exact table and independently checkable simulation certificate together.

The suggested next reduction tests the next decoded bit before the predecessor marker: its zero branch is common to controls 154 and 168. This is an allocation target, not an existing 214-state table. It must preserve the current-one branch and all other uses of borrowed helpers, and must add no replacement state.
