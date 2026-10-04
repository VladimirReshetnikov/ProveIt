# Presentation-only release tools

These owned tools adapt the inspected, release-only Report70 tools. None executes,
imports, or evaluates an upstream scientific checker, simulator, interpreter,
schedule, or Lean source. Scientific Python files under `inputs/` are inert evidence.

## Freeze and preservation

`freeze_inputs.py freeze` was run once to copy the complete authenticated asymptotic
source and independent-audit packets, plus the one-witness closure note, accepted
low-arity audit, and their source manifests. The frozen file count is 46. File bytes,
permission modes, and nanosecond modification times are preserved. Historical
records remain authentic: 132 Report69/70 changes (44 and 88 respectively), with
an unchanged 62-entry core. No whole-historical-release-interval preservation
claim is made. The fresh scoped original inventory additionally covers the actual
Report69 and Report70 release trees and has 994 entries.

Run `python3 -I -S -B tools/freeze_inputs.py verify-originals` only in the original
workspace to compare that fresh scoped inventory. This optional historical-origin
check depends on the original absolute paths. Portable authentication does not:
`python3 -I -S -B tools/release.py check-inputs` verifies the copied frozen inputs.

## Prepare and build

All output locations must be fresh absolute paths outside the release, original
source trees, and protected releases. The author supplies one self-contained
`manuscript/article.tex`. It must not contain external `\\input`/`\\include`
commands. The top-level `article.tex` is an exact copy. The preamble should set
`\\pdftrailerid{}` to remove the path-dependent trailer identifier.

1. `python3 -I -S -B tools/release.py prepare --output-dir /fresh/prepare`
2. Inspect and copy its `article.tex` and `MANUSCRIPT_PINS.json` into their release
   locations. Record the latter file's SHA-256 outside the pin map itself.
3. `python3 -I -S -B tools/build_article.py --pins-sha PIN --bootstrap --output-dir /fresh/bootstrap`
4. Inspect the dependency receipt. Copy `BUILD_DEPENDENCIES.json` to
   `tools/BUILD_DEPENDENCIES_LOCK.json` and record its SHA-256.
5. `python3 -I -S -B tools/build_article.py --pins-sha PIN --dependency-lock-sha LOCK --output-dir /fresh/locked`
6. Copy the accepted PDF to `article.pdf`; use `--require-packaged-match` for
   subsequent locked equality checks.

Every build uses a freshly generated TeX format, a clean environment, a temporary
work directory under the explicit output, disabled shell escape, three TeX passes,
and all-pass recorder input union. A locked build authenticates executable and
system-input bytes before running and verifies the exact executed union afterward.
The precise lock includes the Python interpreter, invoked executables, TeX inputs,
and selected font maps; it does not inventory shared libraries, the Python standard
library, or the operating system. It is not a complete operating-system lock.

Every build extracts the PDF text and renders every page to a 120-dpi PNG by
default, validates page count, PNG chunk CRCs, raster format, and compressed raster
length, and records hashes. Human visual review is separate and must inspect all
pages. Bootstrap is labeled BOOTSTRAP, never a verified locked build.

## Seal, archive, and restore

After all deliverables, QA, and locks are final:

- `python3 -I -S -B tools/release.py manifest --output /fresh/manifest.json`
- Copy that manifest to `RELEASE_MANIFEST.json`; record its SHA-256 separately
- `python3 -I -S -B tools/release.py verify --manifest-sha256 MANIFEST`
- `python3 -I -S -B tools/release.py archive --manifest-sha256 MANIFEST --output /fresh/release.zip`
- Repeat archive creation to a second path and compare whole ZIP bytes
- `python3 -I -S -B tools/release.py extract --manifest-sha256 MANIFEST --archive /fresh/release.zip --output-dir /fresh/extracted`
- Verify and rebuild from the extracted tree with `--require-packaged-match`

The ZIP has deterministic file order, compression, fixed ZIP timestamps, and file
modes. The authenticated manifest records exact original file and directory modes
and nanosecond mtimes; the owned extractor restores them. A generic ZIP extractor
will not necessarily restore those nanosecond times. Root-directory and manifest
self-metadata are intentionally outside the manifest's non-self-referential scope.
Unsafe names, duplicates, symlinks, hardlinks, unexpected inventory, and stale pins
are rejected. Extraction validates every archived payload before creating output.

## Owned tests

`python3 -I -S -B tools/selftest.py --output-dir /fresh/owned-tests` runs synthetic
TeX release tests in external fixtures. It tests fresh-format and locked equality,
first-pass-only dependencies, hostile temporary-directory variables, output safety,
input and manifest tamper rejection, PNG corruption, deterministic ZIP identity,
metadata restoration, and relocated replay. These are owned tool tests, not an
independent scientific audit and not a replacement for manuscript/visual review.
