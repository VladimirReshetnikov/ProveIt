# Further Lean proof simplifications

Four additional directions for `Computability/DiophantineConsistency`, after treating all mechanisms proposed in the specified research packets and incoming archives as prior work.

**Source:** VladimirReshetnikov/ProveIt at `6f46a5e3480a2fa2e45993b8090826f256aeaa56` (26 October 2026).  
**Toolchain:** Lean 4.32.0; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.  
**Main report:** `report/report.pdf`; editable LaTeX in `report/report.tex` and `report/sections/`.

## Recommended patches

| Patch | Mechanism | Physical lines saved, including helpers |
|---|---|---:|
| `01-list-encoding-core.patch` | Identify the exact library list encoding; derive typed parent checking from the existing raw theorem | 4 |
| `03-local-coefficient-fibre.patch` | One exact local coefficient theorem shared by global and selective coding; reuse existing selective zero theorem for separated rows | 20 |
| `04-pell-absolute-minimality.patch` | Use the absolute second coordinate to remove signed cases from fundamental-unit minimality | 8 |
| **Recommended core** | All three above | **32** |
| `02-optional-table-length.patch` | Reuse the library list-length bound | 4 |
| `05-optional-first-exit.patch` | Share interval minimality between the left and right strip-wall proofs | **−13** (adds 13) |

The optional table-length change adds `Classical.choice` to that theorem's dependency set. The corresponding parent-checker theorem already used it. No new axiom is declared. The first-failure abstraction shortens its two applications but increases aggregate production size; it is an optional modularity improvement.

All five patch groups together change 1,693 to 1,670 physical lines and 1,359 to 1,319 nonblank code lines. These are measurements against the real pinned snapshot. They are not estimates for a hypothetical tree containing every earlier proposed refactoring. New production helpers, imports, comments, and blank lines are included in physical-line counts; optional prototypes and validation files are separate.

## What is in the archive

- `report/`: the PDF, LaTeX source, source sections, and a Makefile.
- `patches/`: five independently selectable integration groups and `all-changes.patch`.
- `overlay/`: ten complete resulting production modules at their repository-relative paths, including two new helper modules.
- `validation/`: portable replay script, exact axiom probes, first-failure boundary checks, integrity checker, and pinned toolchain marker.
- `evidence/`: source metrics and hashes, the final 13-check receipt, raw compiler logs, the prior-proposal inventory, a 60-family exclusion ledger, and independent review notes.
- `optional/`: compiled mixed-product coefficient and Pell minimum-coordinate prototypes. They are outside the production patch and all savings totals.
- `MANIFEST.sha256`: SHA-256 digests of all other packaged files.

## Formal verification scope

All ten complete changed or new production modules compiled together successfully, including the full `NativePellBootstrap` file. Two boundary examples and the baseline/candidate axiom probes also compiled. The final receipt has 13 successful checks: 10 production modules, one boundary-check file, and two axiom-report files. The combined patch passed `git apply --check` against the pinned baseline.

The axiom audit includes every changed existing theorem and all three new production helper theorems. The only change in an existing theorem's reported axiom set is the optional table-length theorem's added `Classical.choice`. No inspected final declaration depends on `sorryAx`. Public theorem signatures and executable definitions are preserved.

This is a targeted build against the required production dependencies. It is not a repository-wide rebuild, a controlled speed benchmark, or a comparison of kernel proof-term size. The elapsed times are records of individual validation runs only.

## Reproduce without changing the source checkout

Use a checkout of the recorded source pin with its Lean toolchain and Mathlib dependencies available. Python 3.10 or later is recommended. From the extracted archive directory:

```sh
python3 validation/verify_bundle.py
python3 validation/replay.py --repo /absolute/path/to/ProveIt --output /absolute/path/to/replay-output
```

The replay script verifies the exact baseline and overlay source hashes. Its normal mode builds the eight existing target modules through Lake, obtains the selected compiler and import search path from `lake env`, and checks the overlay in a separate output directory. It does not apply the integration patches or overwrite the repository's source files. Its output directory must be new or empty. See `python3 validation/replay.py --help` for prepared-cache and optional-prototype options.

The original run used an explicitly pinned local compiler and dependency cache. `--config` supports the equivalent explicit-environment mode; ordinary users should use the default Lake-based mode. In either mode the staged namespace contains unchanged dependency artifacts as well as the proposed modules, avoiding Lean's sparse-namespace search-path problem.

## Integrate selectively

The full overlay files are reference after-files from the pinned experiment. On a branch where the earlier proposals have been adopted, rebase the targeted proof changes rather than replacing whole files. That preserves the already-applied improvements required by the task premise.

Against the exact baseline, check each selected patch from the repository root. For example, with the extracted bundle at `/absolute/path/to/bundle`:

```sh
git apply --check /absolute/path/to/bundle/patches/01-list-encoding-core.patch
git apply --check /absolute/path/to/bundle/patches/03-local-coefficient-fibre.patch
git apply --check /absolute/path/to/bundle/patches/04-pell-absolute-minimality.patch
```

After review, apply the chosen files with `git apply` and run the project's normal build gates. Patch 02 requires patch 01's encoding bridge. Patch 03 contains the new `QuadraticFiber.lean` file; patch 05 contains the new `FirstExit.lean` file. Patches 03, 04, and 05 do not depend on patch 01. Use `all-changes.patch` only when choosing every group, including both optional changes.

Suggested review order: the coefficient theorem's exact pair fibre and diagonal case; the isolated Pell edit; the library-encoding bridge and parent theorem specialization; then the two optional tradeoffs.

## Rebuild the report

Install XeLaTeX with `fontspec`, `fvextra`, and the standard packages used in the source. The report uses Bitstream Charter, DejaVu Sans, and DejaVu Sans Mono. From `report/`:

```sh
make
```

The three XeLaTeX passes resolve the table of contents, pagination, and references from a clean build. The delivered PDF was rendered and visually inspected after compilation.

## Novelty and provenance

The audit covers the six placed packets, five incoming ZIPs, eleven principal manuscripts, 329 inventory files, and 400 archive members. The latter two figures describe inventory coverage; they do not mean every incidental binary or copied source received an independent semantic review. Proposed, deferred, design-only, and rejected historical mechanisms are all treated as excluded. The ledger records precise source/member references.

“Additional” means additional relative to that audited corpus. The report makes no global novelty claim for elementary mathematics or common Lean proof techniques. The copied source after-files derive from the repository at the pinned commit; patches and report identify the exact modifications. Stable upstream source links are in the report bibliography. No generated equation databases, compiler binaries, or dependency caches are included.
