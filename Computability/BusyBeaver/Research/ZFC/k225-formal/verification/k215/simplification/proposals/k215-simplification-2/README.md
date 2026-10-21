# K215 proof simplification and checked CM215 transfer

Research packet, 21 October 2026, for incorporation into ProveIt.

**Main result:** a new, compiled Lean theorem transfers blank halting between
CM215 and the exact existing `KDense215.machine215`. CM215 is an existing
215-state alternative. **No 214-state machine is claimed or supplied.**

The complete account is in `report.pdf`, with editable source `report.tex`
and `plain_lane_results.tex`. All repository comparisons use commit
`b6c7087477e51c017003bd729e712c8969733223`.

## What is included

| Directory | Result and boundary |
|---|---|
| `formal_cm215/` | Lean 4.32.0 checked positive simulation, three-clause invariant, arbitrary-initial-tape native equivalence, and exact dense/Core equivalence. Minimal upstream dependencies are included. The final full-ZFC adapter is supplied but was not compiled here. |
| `proof_audit/` | Audit of already completed upstream simplifications; new shared-tree/path-codec generators, source prototypes, exact identities and measurement records. |
| `coq/` | Exact compact/original certificate equality and a symmetry theorem for the actual offset checker, compiled and recursively checked with Coq 8.18.0. No fresh Rocq 9.1 endpoint replay is claimed. |
| `plain_source/` | Checked ordinary zero-offset source equivalence for every register file, with all 70 modules and exact tree/DAG bindings. Includes a serial fresh-build runner. |
| `reduction_search/` | New bounded negative searches on final 215-state seeds; exact bounds, inputs and scripts; a second marker-fold opportunity and its unresolved provider problem. No minimality claim. |
| `evidence/` | Independent reviews and exact table comparisons performed within this collaboration. |

## Quick verification

From the packet root:

```sh
python3 verify_archive.py
python3 formal_cm215/verify_packet.py
python3 -B reduction_search/code/check_near_miss.py
```

The first command verifies every file against `MANIFEST.sha256.json`; it does
not recheck proof objects. The CM215 checker verifies literal bindings and a
small independent finite corroboration. Kernel checks use the commands below.
No machine has been accepted merely because it agrees on a finite blank run.

### Rebuild the checked CM215 theorem

With Lean 4.32.0 and Python 3, offline and without mathlib:

```sh
python3 formal_cm215/build.py --lean /path/to/lean --out /fresh/cm215-build
```

Builds are serial. The final target is
`CM215Core.blank_halts_iff_primary`. The strongest native theorem is
`CM215Exact.all_tapes_equihalt`, from initial control 0 for every tape and head.
For the final consistency statement, compile `CM215ZFCAdapter.lean` in the
existing full ProveIt ZFC environment. That final adapter is explicitly
outside this packet's fresh build record.

### Rebuild the Coq equality and symmetry proofs

Use Coq 8.18.0 for the recorded environment, or the repository's current Rocq
version for an integration replay. The certificate equality is self-contained:

```sh
python3 coq/build.py --out /fresh/certificate-build --certificates-only
```

The actual-checker symmetry additionally needs exactly two hash-pinned K230
reference sources. Supply an existing checkout, or request their download:

```sh
python3 coq/build.py --out /fresh/coq-build --reference /path/to/k230-rocq
python3 coq/build.py --out /fresh/coq-build --fetch-upstream
```

The helper runs `coqc`, records source hashes, and runs recursive `coqchk`.
`coq/README.md` explains version and licensing boundaries. A source patch
shows how to replace the second computed certificate proof with the new
forward-only theorem; downstream endpoint adoption still requires rebuilding.

### Rebuild the ordinary source equivalence

With Lean 4.32.0, offline:

```sh
python3 plain_source/build.py --lean /path/to/lean --output /fresh/plain-source-build
```

This serially checks the exact source program through the actual iterative
DAG semantics. It does not replay the complete binary-to-ZFC endpoint.

### Rebuild the PDF

```sh
sh build_pdf.sh
```

This requires a TeX Live installation with the standard packages named in
`report.tex`. Rebuilding sources or the PDF may change hashes; the manifest
records the exact delivered artifact, not all future regenerated versions.

## Recommended integration sequence

1. Add the compact CM215 proof and compile its final adapter against the
   existing endpoint closure.
2. Add the Rocq mirror theorem and derive the backward check from the forward
   one; rebuild the affected production modules with pinned Rocq.
3. Adopt the compact certificate and shared trees, retaining exact equality
   witnesses and updating source/object hash records.
4. Evaluate the ordinary source-checker specialization with its full-length
   path decoder; do not substitute the old 128-bit decoder.
5. Continue 214-state synthesis against the explicit continuation contract in
   the report. Failed bounded joins are inconclusive beyond the tested family.

No unconditional nonhalting assertion, internal PA formalization for 215 states,
or global state-count lower bound is claimed. See `NOTICE.md` for attribution.
