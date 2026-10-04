# Presentation-only release tools

These owned tools adapt the fully inspected presentation-only tools from the
previous, separately delivered fixed-order article. No tool executes, imports or
evaluates a supplied scientific checker, interpreter, simulator, schedule or Lean
source. Every program retained beneath `inputs/`, including the predecessor's
release tools, is inert evidence. Only the current top-level `tools/` programs
are used for presentation replay.

## Evidence and preservation boundary

`freeze_inputs.py freeze` authenticated the complete new proof and independent
audit through their pinned SHA-256 manifests and adjacent ZIPs, and copied both
packets plus their ZIPs and receipts without changing source bytes, permission
modes or nanosecond modification times. It additionally authenticated and copied
the complete predecessor article release and its archive. There are 213 frozen
files and 26 directories beneath `inputs/` (excluding the `inputs` root).

The original preservation inventory covers 355 filesystem objects: the new proof
and audit trees and seals, the predecessor tree and archive, and every object in
the independent audit's existing 333-object boundary. The earlier source's
51-object preservation records are equal and are contained in that verified
boundary. Checks cover object sets, file sizes and hashes, permission modes and
nanosecond mtimes. Access times, ctime, owner, inode allocation and directory
allocation sizes are excluded. Original content or metadata is never repaired to
make a check pass. Historical evidence is preserved as supplied, including the
predecessor's explicit account of older Report69/70 changes; no whole-historical-
workspace preservation claim is made.

`python3 -I -S -B tools/freeze_inputs.py verify-originals` checks this scoped
original boundary only in its original workspace. Portable authentication does
not require those absolute sources: `python3 -I -S -B tools/release.py check-inputs`
verifies the copied evidence and its metadata against `INPUT_PINS.json`.

## Prepare and build

Read every tool in full before execution. Output paths must be fresh, absolute,
and outside the release and protected originals. The author supplies one
self-contained `manuscript/article.tex`; no external input/include is permitted.
The top-level `article.tex` must be byte-identical. Include `\pdftrailerid{}` in the
preamble to suppress path-dependent PDF trailer identifiers.

1. `python3 -I -S -B tools/release.py prepare --output-dir /fresh/prepare`
2. Inspect and copy its `article.tex` to the release root and its
   `MANUSCRIPT_PINS.json` to `manuscript/`. Record the latter's SHA-256 externally.
3. `python3 -I -S -B tools/build_article.py --pins-sha PIN --bootstrap --output-dir /fresh/bootstrap`
4. Inspect its dependency record. Copy `BUILD_DEPENDENCIES.json` to
   `tools/BUILD_DEPENDENCIES_LOCK.json` and record that file's SHA-256 externally.
5. `python3 -I -S -B tools/build_article.py --pins-sha PIN --dependency-lock-sha LOCK --output-dir /fresh/locked`
6. Copy the accepted PDF to `article.pdf`. Use `--require-packaged-match` for
   subsequent locked equality builds.

A build creates a fresh TeX format in an explicit external temporary directory,
uses a clean environment and selected lm/cm font maps, disables shell escape,
and compiles exactly three times. The dependency union includes the format
recorder and all three compilation recorders, so first-pass-only dependencies
are not lost. Locked replay checks hashes before execution and checks the
executed dependency union afterward. A bootstrap is labeled BOOTSTRAP, never a
verified locked replay.

The lock covers seven interpreter/executable entries, recorded TeX system inputs
and selected font maps. It does not inventory shared libraries, the Python
standard library or the operating system, and is not a complete environment lock.
Every build extracts PDF text and renders every page to PNG (120 dpi by default),
checking page count, chunk CRCs, raster structure and decompression length. Visual
review of every page is separate and remains necessary.

## Seal and restore

Do not seal until mathematical/manuscript review, visual review, README, QA,
all tools, dependency locks and deliverables are final.

- `python3 -I -S -B tools/release.py manifest --output /fresh/manifest.json`
- Copy it to `RELEASE_MANIFEST.json`, recording its SHA-256 separately
- `python3 -I -S -B tools/release.py verify --manifest-sha256 MANIFEST`
- `python3 -I -S -B tools/release.py archive --manifest-sha256 MANIFEST --output /fresh/release.zip`
- Repeat archive creation to a second fresh path and compare all ZIP bytes
- `python3 -I -S -B tools/release.py extract --manifest-sha256 MANIFEST --archive /fresh/release.zip --output-dir /fresh/extracted`
- Verify and rebuild from the restored tree with `--require-packaged-match`

ZIP members have deterministic ordering, compression, timestamps and modes. The
manifest records all non-self-referential file and directory modes and nanosecond
mtimes. The owned extractor validates every payload before creating output and
restores those recorded modes and mtimes. Root-directory metadata and the
manifest's own metadata are intentionally excluded. The manifest is stored in the
ZIP with normalized mode 0644; a read-only delivery copy can therefore have mode
0444 without contradicting that boundary. Generic ZIP extractors need not restore
nanosecond mtimes. SHA-256 pins and read-only permissions provide local integrity
conventions, not a digital signature, WORM storage or trusted external timestamp.

## Owned hostile-input tests

`python3 -I -S -B tools/selftest.py --output-dir /fresh/owned-tests` uses synthetic
TeX in external fixtures. It tests locked PDF equality, all-pass recording,
hostile temporary-directory variables, output/source overlap and symlink
refusals, stale pins, content/mode/mtime and inventory tampering, malformed PNGs,
manifest collisions, deterministic ZIP equality, path traversal rejection,
metadata-restoring extraction and relocated exact PDF replay. These are owned
presentation-tool tests, not a scientific rerun or independent review.
