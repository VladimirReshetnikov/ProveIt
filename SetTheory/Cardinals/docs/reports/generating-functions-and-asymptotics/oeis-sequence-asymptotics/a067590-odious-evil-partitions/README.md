# Report 165 — Odious and evil integer partitions

This is a local, self-contained article and exact-check package. The article
proves the two July 2025 equivalents recorded as conjectures in OEIS A067590 and
A116492, derives the evil counterparts A067591 and A116491, and gives every
fixed algebraic order. For each fixed cap m, the odious/evil ratio is m+1 to all
algebraic orders. Smooth Bessel comparison inverses and rounding-aware ordinary
first thresholds are included.

The PDF is the reading copy; Report165.tex is its editable LaTeX source.
SOURCE_PROVENANCE.json records exact sources, inspection scope, source hashes,
and all three repository Atlas overlaps. Original source PDFs and full external
articles are not redistributed. See the bibliography and source provenance for
links. The manuscript preserves the unread Merca full-text and original
Allouche–Cohen 1985 paper caveats; it makes no historical-priority claim.

## What is and is not certified

The proofs establish fixed-cap and fixed-order asymptotic statements. The
companion supplies exact finite checks for ten families through n=512,
independently structured product and Euler constructions, the complete four
OEIS displayed prefixes, three rational Bessel-coefficient checks through order
6, and formal inverse algebra checked in two ways. Its exact threshold routine
scans from n=0 without presuming monotonicity.

No decimal constant is interval-certified. The numerical illustrations have
ordinary binary64 roundoff and do not certify an asymptotic error or onset.
No claim concerns growing caps or the leading beyond-all-orders correction.
Finite inverse formulas must not be rounded blindly to obtain integer answers.

## Contents

- Report165.pdf and Report165.tex
- companion/: standard-library code, tests, frozen numerical prefixes, reference
  exact JSON and separately labeled numerical illustrations, and its full README
- SOURCE_PROVENANCE.json: source identities, credit, scope and caveats
- build_pdf.py: clean deterministic-metadata PDF build
- make_zip.py: allowlist/checksum-verified deterministic stored ZIP
- release_tools.py and test_release.py: exclusive descriptor-pinned I/O and tests
- RELEASE_RECEIPT.json: local verification results and all-page review record
- SHA256SUMS: frozen hashes for the complete archive allowlist

Only the allowlisted files enter the archive. Build directories, rendered page
images, caches, unlisted files and external source documents do not enter it.
The manifest is an integrity/replay aid, not a cryptographic signature.

## Run the exact checks

Python 3.10 or newer is required. The companion uses only the standard library.
From the physical report directory:

```sh
cd companion
python3 -B -m unittest -v test_companion
python3 -B -O -m unittest -v test_companion
python3 -B companion.py --output-parent "$(pwd -P)" --output-name new_run
```

Use a new output name. Existing destinations are deliberately refused. Compare
new_run/exact_results.json with reference_run/exact_results.json byte for byte.
Numerical JSON is replayable on the tested Python/math-library platform, but its
last digits are not promised identical on arbitrary platforms. The command line
has no precision, tolerance, order or workload control.

## Rebuild the PDF

The release build requires Linux/POSIX, /proc/self/fd, Python, pdftex/pdflatex,
and the TeX packages used in the source (including Latin Modern, amsmath,
mathtools, geometry, microtype, hyperref and fancyhdr). It uses the installed
TeX distribution and isolates user TeX settings. No network is used.

```sh
python3 -B build_pdf.py --output-dir "$(pwd -P)/new_pdf_build"
cmp Report165.pdf new_pdf_build/Report165.pdf
```

The output parent must already exist, be owned by the current user, and not be
group- or world-writable. Its path must not contain symlinks. The destination
must not exist. The build creates a private directory, compiles a clean format,
uses no shell escape, fixes metadata, and runs until references stabilize
(up to six passes). A settled warning, overfull box, underfull box or missing
character is an error. Reproduction was checked twice in the provided TeX
installation; byte equality across arbitrary TeX versions is not promised.

## Rebuild the source ZIP

From the report directory:

```sh
python3 -B -m unittest -v test_release
python3 -B -O -m unittest -v test_release
python3 -B make_zip.py --output "$(pwd -P)/new_source.zip"
```

The archive builder verifies SHA256SUMS against a fixed sorted allowlist before
writing anything. It uses sorted paths, stored members, fixed timestamps and
fixed permissions. Existing output files, directories, symlinks, dangling
symlinks, parent symlinks and parent traversal are refused. Parent descriptors
stay pinned during writes. No overwrite or cleanup option is provided; an
incomplete private artifact may remain after a failed operation and is not
silently reused. These defenses assume the parent and executing account are
trusted; they do not isolate against root or a hostile process of the same user.

Local preparation involved no upload, publication, external contact, OEIS edit,
repository modification, or change to earlier reports.
