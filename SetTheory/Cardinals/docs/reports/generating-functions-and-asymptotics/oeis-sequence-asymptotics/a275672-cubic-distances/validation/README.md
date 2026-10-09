# Independent validation bundle

This directory contains the bounded validation performed for the exact-search programs in the A275672 report. It includes unmodified source snapshots, a simple independent subset-enumeration reference, recorded results, and a portable reproduction script.

The written audit explains why the search is complete. Regression tests provide additional evidence and help detect implementation changes; they do not replace the completeness proof or the complete large-grid case records elsewhere in the research package.

## Reproduce the checks

Requirements: Python 3.9 or later and a C++17 compiler accepting the usual GCC/Clang command-line flags. Run without Python's `-O` option, because assertions are part of verification.

From this directory:

```bash
python run_audit.py --output audit_output
```

The script compiles in a temporary directory, compares the three recursive search implementations with the independent reference on 500 generated instances each, and runs 256 small-grid diameter cases across four modes. It writes results and full new stdout/stderr logs into the chosen output directory. Compilation and each subprocess have time limits; an unknown result, mismatch, invalid witness, or nonzero exit stops the audit.

To audit other source files:

```bash
python run_audit.py \
  --v5 ../src/rainbow_exact_v5.cpp \
  --top2 ../src/rainbow_top_edges.cpp \
  --prefix ../src/rainbow_edge_prefix6.cpp \
  --output audit_output
```

The corresponding environment variables are `A275672_AUDIT_V5`, `A275672_AUDIT_TOP2`, and `A275672_AUDIT_PREFIX`. Compiler selection is available through `--cxx clang++` or `A275672_AUDIT_CXX`. No workspace-specific absolute paths are embedded in the bundle.

The default snapshot profiles are listed in `source_manifest.json`. An overridden source's hash is recorded in the output; passing the bounded tests for a modified source does not transfer the manual source audit automatically to that modification.

## Recorded checks

### Recursive-search comparison

Each of the three implementations matched a straightforward exhaustive subset enumerator on 500 random induced instances: 250 in the side-four grid and 250 in the side-five grid. Each run produced 317 SAT and 183 UNSAT instances. Every SAT witness was checked for distinct squared distances.

The generator uses `std::mt19937` with seed `20261008`, up to 18 candidates, and between zero and three already selected points. The reference performs only direct distance checks and an elementary remaining-count bound. It does not use the optimized search's compatibility graph, graph coloring, core pruning, parity occupancies, or symmetry reductions.

The source fully specifies all 500 checks. `std::shuffle` can produce different permutations with a different C++ standard-library implementation; that may change the SAT/UNSAT totals, but every generated instance must still agree with the independent reference. The original compiler version is recorded in `source_manifest.json`.

### Diameter and edge-prefix cases

All cases in the following table were run separately in four modes: v5 diameter anchoring, top-two-edge anchoring, top-three-edge anchoring, and top-four-edge anchoring.

| Side length | Target size | Diameter cases | SAT cases | UNSAT cases | Program runs |
|---:|---:|---:|---:|---:|---:|
| 3 | 4 | 6 | 4 | 2 | 24 |
| 4 | 5 | 19 | 15 | 4 | 76 |
| 4 | 6 | 6 | 4 | 2 | 24 |
| 5 | 7 | 27 | 19 | 8 | 108 |
| 5 | 8 | 6 | 0 | 6 | 24 |
| **Total** | | **64** | **42** | **22** | **256** |

Every variant agreed on every case. The diameter orbit counts were independently enumerated in Python. Every returned SAT point set was independently checked using integer squared distances. The reproduction runner additionally verifies that its unique longest edge is the requested diameter representative.

`recorded/diameter_prefix_results.json` retains the 256 status/node records; `recorded/diameter_prefix_summary.json` summarizes them. `recorded/random_search_results.json` retains the three reference-comparison summaries. The reproduction runner preserves full stdout/stderr from newly run checks.

### Focused review of the complete side-eight run

`audit_n8_release.py` independently verifies the frozen release manifest, the exact source snapshot, all diameter orbits needed for the target of thirteen points, the complete run's summary/log agreement, and the twelve-point lower-bound witness. It does not rerun the expensive impossibility search.

```bash
python audit_n8_release.py --release-dir ../exact_search/release --output n8_audit.json
```

The release directory can instead be supplied through `A275672_RELEASE_DIR`; adjust the relative path to the layout of the research package. `recorded/n8_release_audit.json` records the observed checks. The independent enumeration found 660 eligible unordered edges, exactly the 23 logged cube-isometry orbits, and the diameter threshold 101. All recorded cases were UNSAT, with final totals of 38,430,195 inner search nodes and 445.028 seconds. The twelve-point witness has 66 distinct squared distances.

`N8_RELEASE_AUDIT.md` explains the scope, necessary radial and parity conditions, and the limit of this record audit: the individual UNSAT results still depend on the reviewed exhaustive-search implementation and its execution, rather than on a separate formal proof certificate.

### Integer-only modulo-four diameter certificates

```bash
python verify_mod4_diameter.py --output mod4_diameters.json
```

This enumerates all weak compositions of each target size into the eight coordinate-parity classes. It proves that thirteen points in the side-eight grid would require squared diameter at least 102; fifteen points in side nine would require at least 149; and seventeen points in side ten would require at least 209. These statements are necessary conditions, not existence results. The recorded occupancies, exact palette capacities, and enumeration counts are in `recorded/mod4_diameter_certificate.json`.

## What was manually audited

`SEARCH_AUDIT.md` covers the recursive invariant, every pruning rule, the unique-diameter case split, the stabilizer reduction, the second-largest edge split, and induction for an arbitrary processed edge prefix. `ARTICLE_AUDIT.md` covers the asymptotic mathematics and finite Gaussian bound code.

The later `rainbow_edge_prefix6.cpp` snapshot differs from the tested top-four-prefix source in one line: it also accepts mode names `top5` and `top6`. The prefix recursion is unchanged. Its generic completeness argument is covered by the manual audit. No separate top-five/top-six regression batch is represented in the recorded results.

Two additional snapshots, `rainbow_filtered.cpp` and `rainbow_prefix_filtered.cpp`, add necessary occupancy and radial tests before the diameter or prefix enumeration. Their source diffs were reviewed separately in `FILTERED_SEARCH_AUDIT.md`; no independent regression batch for those snapshots is represented here. The original side-eight proof source is unchanged.

This bounded audit does not rerun the complete side-seven or larger impossibility computations. The main package provides their source hashes, completed case records, and reproduction instructions.

## Files

- `run_audit.py`: portable bounded reproduction runner.
- `audit_n8_release.py`: independent frozen-release, orbit-coverage, log, and witness checks.
- `verify_mod4_diameter.py`: exact finite occupancy certificate for necessary diameters.
- `random_reference_harness.cpp`: independent subset reference and seeded instance generator.
- `sources/`: unmodified versions examined during the audit.
- `source_manifest.json`: source hashes and original audit environment.
- `SEARCH_AUDIT.md`: logical audit of exact search.
- `ARTICLE_AUDIT.md`: mathematical and finite-bound audit.
- `N8_RELEASE_AUDIT.md`: focused review of the complete side-eight records and diameter constraints.
- `FILTERED_SEARCH_AUDIT.md`: focused review of later diameter and prefix occupancy filters.
- `recorded/`: observed audit outcomes.
- `SHA256SUMS`: checksums of all other files in this bundle.
