# Report 67

## Positive POWER reductions and exact bounded compiler costs

4 October 2026. The complete 24-page article is `Report67.pdf`; `Report67.tex` is its deterministically flattened editable source. Eight readable source modules are in `manuscript/`.

Five explicitly displayed positive POWER modules have 22/16/14/13/12 leaves including output and 15/9/7/6/5 residual slots. Their exact fixed-base SOS degrees are 12/12/16/16/20; the last two variable-base degrees are 20 and 24. Every adapter, witness-map direction, recovered integral and positive domain, and infinite-fiber argument is proved. The last map is a bijection only with the old strict-quotient subset; an explicit excluded endpoint illustrates why this matters.

The retained three-witness bounded compiler has exact degree 2 at T=0, 4(T+1)^2-4 at positive odd T, and 4(T+1)^2-8 at positive even T. The article proves the leading coefficient and its sign at all horizons, identifies the entire top homogeneous monomial, sharpens the support ceiling, and pays for finite tables, coefficient height and expanded storage. With two complete twelve-leaf modules, the native-gap composition has 29 positive witnesses, three external inputs, 32 variables, 18 residual slots and degree max(20,compiler degree). Other tradeoffs and the complete finite-trace alternative are tabulated. A vector diagram distinguishes normalization, bijections and strict-domain restriction.

All complete POWER and composed fibers are infinite despite unique decoding and unique compressed projection. This is a horizon-indexed family, not one fixed polynomial for unbounded halting. No new Lean verification, novelty, priority, minimality, universal-polynomial record, arithmetic-gate improvement or efficient Pell-witness claim is made. Physical transport uses only the retained encoded-input compiler theorem.

## Included material and exact execution boundary

- `science/power-baseline/`: unchanged 22/16/14/13 module packet and dependency-preserving inert copies
- `science/power-twelve/`: unchanged twelve-leaf packet and dependencies
- `science/exact-degree/`: unchanged exact interpolation-degree packet and dependencies
- `science/bounded-certificates/`: unchanged accepted bounded compiler from Report66, including native-gap, trace and physical proofs
- `audits/power-baseline/`, `audits/power-twelve/`, `audits/exact-degree/`: unchanged accepted independent mathematical dossiers
- `INPUT_PINS.json`: frozen copied bytes and file/directory metadata with source origins
- `qa/`: presentation receipts, source comparisons, tool lineage and completed reviews
- `tools/`: newly adapted Report67 presentation, release and synthetic selftest tools
- `RELEASE_MANIFEST.json`: the final exact payload inventory, externally authenticated

Scientific programs, upstream sources and mathematical-audit checkers are inert evidence. The report tools never import or execute them. No machine interpreter, physical simulator, saved schedule, author scientific program, upstream implementation or Lean is run. `qa/prepare_presentation.py` is an inspected one-time authoring record with historical workspace paths; it is not a portable replay entry point. `qa/prior-release-tools/` contains inert inspected Report66 lineage. Use only the current `tools/` entry points for presentation replay.

All three mathematical continuations have separately accepted independent audits. The exact-degree audit's one local scope clarification is incorporated: the symmetry degree bound for odd K applies to K>=3, with K=1 handled separately. The twelve-leaf audit's domain challenges concern reconstruction under changed domains, not false-output counterexamples to the stated theorem. Manuscript and release-tool reviews are pending for this candidate; final receipts will be included before sealing.

## Authenticate a received release

Use Python 3.9 or newer and inspect `tools/release67.py` before execution. Obtain EXPECTED_MANIFEST_SHA256 from outside the archive. Hashing a manifest stored inside an untrusted archive is not external authentication.

    python3 -I -S -B tools/release67.py verify --manifest-sha256 EXPECTED_MANIFEST_SHA256

Verification authenticates the exact file and directory descendant inventory, regular single-link files, byte sizes, SHA-256 hashes, modes and nanosecond modification times. It rejects symlinks, special files, unexpected entries and empty directories. The manifest itself is authenticated by its external digest; its own filesystem metadata and the top-level release root's metadata are outside that inventory. Operation snapshots nevertheless check preservation of the current root. Access times are not integrity evidence, and creation/change timestamps are not transported.

For an ordinary ZIP file, generic extractors may discard authenticated nanosecond times. From an inspected tools copy use:

    python3 -I -S -B tools/release67.py extract --archive /absolute/path/Report67-source-evidence-20261004.zip --output-dir /absolute/path/new-report67 --manifest-sha256 EXPECTED_MANIFEST_SHA256

The extractor authenticates the manifest and exact member list before writing, verifies bytes and file modes, rejects traversal/nonregular entries, and restores descendant file and directory modification times. The new root is mode 0700. The manifest is assigned mode 0644 and the fixed epoch. ZIP container timestamps, compression choices, comments and other container metadata are not independently authenticated by extraction. The destination must be fresh and outside the release and protected input roots. Verify again from the extracted copy.

## Locked byte-identical PDF rebuild

Inspect `tools/build_report67.py` and its hash-pinned release helper. The reviewed manuscript-pin map is:

`99a8beb275e70e66aa4426f1497ccad79a2a4ed13617cce7e6d912ec98a11656`

The article's dependency-lock pin is:

`924a24fab30a2e05eccd168d7951273e31b99a8adbb3290ab5d8b6f332b884e1`

After authenticating the release:

    python3 -I -S -B tools/build_report67.py --output-dir /absolute/path/new-report67-build --pins-sha 99a8beb275e70e66aa4426f1497ccad79a2a4ed13617cce7e6d912ec98a11656 --dependency-lock-sha 924a24fab30a2e05eccd168d7951273e31b99a8adbb3290ab5d8b6f332b884e1 --require-packaged-match

This uses a fresh local TeX format, fresh font map, allowlisted environment, disabled shell escape and three LaTeX passes. The lock covers named interpreter/executable bytes and the complete union of format and every pass's recorded system TeX/font inputs plus selected font maps. It does not inventory shared libraries, Python's standard library or the operating system. A changed toolchain must fail preflight rather than count as an identical rebuild.

The output contains the byte-identical PDF, extracted text, all recorder receipts, a dependency receipt, page PNGs and raster inventory, source-preservation records and a build receipt. Automated CRC/raster checks are separate from visual review of every page. Fixed SOURCE_DATE_EPOCH is 1791072000; PDF dates and trailer IDs are omitted. `--bootstrap` is an authoring-only route that records an initial dependency set; it does not claim preflight lock verification and must not replace the locked replay.

## Deterministic archives and owned selftests

    python3 -I -S -B tools/release67.py archive --manifest-sha256 EXPECTED_MANIFEST_SHA256 --output /absolute/path/new-report67.zip

Creation sorts all files under `Report67/`, fixes the ZIP timestamp, preserves authenticated modes and uses deterministic deflate settings. These are creation guarantees, distinct from the extraction authentication boundary. Repeated creation in the same Python/zlib environment must be byte-identical. Do not regenerate a manifest to make a changed received release pass.

    python3 -I -S -B tools/selftest67.py --output-dir /absolute/path/new-report67-selftest

The owned synthetic tests cover pins, source/output aliases, frozen metadata, first-pass-only TeX dependencies, inherited hostile temporary variables, corrupt PNGs, deterministic archives, metadata-preserving extraction, relocated verification and identical PDF rebuilding. They do not execute mathematical software and are not independent review. Their final receipt records the actual completed checks.

## Attribution

The unchanged mathlib source is Mario Carneiro and contributors' `PellMatiyasevic.lean`, commit `ac77769fabe23cb237559e7f56578dbead91499f`, SHA-256 `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`. Original headers, Apache 2.0 license and notice are retained with all dependent source copies. The article credits the exact theorem pair. Earlier research proofs, scientific checkers and audit programs retain their identity and are not presented as newly authored report software.
