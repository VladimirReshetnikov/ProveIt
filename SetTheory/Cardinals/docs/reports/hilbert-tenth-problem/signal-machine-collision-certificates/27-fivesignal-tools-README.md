# Report57 release tools

These freshly authored Python standard-library tools do not execute scientific
source programs, author/upstream checkers, saved programs, or physical simulation.
The independent auditor's replay adapter is a separate entry point.

All commands use `python3 -I tools/release.py` (without `-O`). The tool locates
its release root from its own location, so moved and extracted copies work.

## Workflow

1. Prepare stable `Report57.tex`, `assets/guards.tex`, and `assets/rules.tex`.
2. Build into an absolute, fresh, external directory:
   `python3 -I tools/release.py build-pdf --draft --output /absolute/new/build-a`
3. Repeat into another fresh directory. To bind TeX dependencies, pass
   `--dependency-lock /absolute/new/build-a/dependency-manifest.json` and
   `--dependency-lock-sha256 HASH_OF_THAT_FILE`. Compare the PDF hashes and
   inspect rendered pages. Copy the approved PDF into `Report57.pdf` using an
   exclusive creation operation. Finish all review/receipt files before sealing.
4. Run `python3 -I tools/release.py seal` once. Preserve the printed manifest
   SHA256 through a trusted channel outside the archive. The manifest does not
   include itself; its trusted hash supplies that final integrity link.
5. Run `python3 -I tools/release.py verify --manifest-sha256 TRUSTED_HASH`.
6. A sealed PDF rebuild omits `--draft`, adds `--manifest-sha256 TRUSTED_HASH`,
   and must exactly reproduce the packaged PDF. A dependency lock may also be
   supplied. Every output directory must be fresh and external.
7. Run `python3 -I tools/release.py archive --manifest-sha256 TRUSTED_HASH
   --output /absolute/new/Report57.zip`. Repeat under a new filename to check
   the ZIP hash. Extract with POSIX modes preserved, then verify again.

## Safety and reproducibility

- No existing output is replaced, merged, truncated, cleaned, or deleted.
  Existing files/directories, live/dangling symlinks, missing ancestors,
  special files, hardlinked inputs, source/output overlap and symlink ancestors
  are refused. Failures retain any newly created diagnostic output for review.
- Seal requires canonical 0755 directory and 0644 file modes; it never changes
  source permissions. Exact inventory includes empty directories. Verification
  binds content, lengths, inventory and modes to the trusted manifest SHA256.
- Builds copy only the three stated plain LaTeX inputs to a fresh directory.
  Each run creates its own TeX format, font map, home and cache. The environment
  is constructed from scratch, without inherited TEXINPUTS or similar settings.
  Shell escape is disabled, TeX restrictive input/output settings are set, and
  the fixed source epoch is 1791072000 (2026-10-04 00:00:00 UTC).
- Three PDF passes are required. Final unresolved references/citations, rerun
  warnings and overfull boxes fail the build. PDF metadata that could embed
  dates or output paths is suppressed through the compiler input prefix.
- TeX dependency receipts pin the recorded installed TeX file inventory and
  executable bytes. They do not claim to pin dynamically linked OS libraries.
  Original LaTeX input hashes appear separately in the build receipt.
- Archives use sorted paths, ZIP_STORED, fixed 2026-10-04 timestamps, fixed
  modes, no comments or extra fields, and verified member content/CRC.
- Build/archive check preservation of release bytes, modes, mtimes and file
  identity. The release must be quiescent while a command runs. This integrity
  utility is not an operating-system sandbox against hostile TeX or concurrent
  malicious filesystem mutation; run only reviewed LaTeX on a trusted host.

## Synthetic adversarial tests

`python3 -I tools/test_release.py --output /absolute/new/test-root --with-pdf`

Tests use only newly created disposable fixtures, never the real manuscript.
They cover preservation/rejection cases, tampering, hardlink/symlink/special-file
guards, trusted pins, isolated execution, deterministic synthetic PDF builds,
dependency locking, deterministic archives and moved/extracted verification.
The output directory contains a JSON receipt and all retained diagnostics.
