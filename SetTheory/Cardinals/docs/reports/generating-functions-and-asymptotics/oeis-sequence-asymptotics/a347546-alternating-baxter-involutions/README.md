# Report 149

Corrected enumeration and asymptotics of alternating Baxter involutions

The permutation class intended by OEIS A347546 has 2168 objects at length 20, rather than the published 2166. The two outside blocks are inverse partners and need not separately be involutions. The corrected Catalan outside factor gives algebraic generating functions, exact growth rate sqrt(1+sqrt(5)) per permutation entry, every fixed asymptotic order, and Lambert-W parity inverses with ceiling-safe asymptotic brackets.

The all-length enumeration proof uses explicitly identified unrestricted structural lemmas from Min and Park (2006), with both construction directions, uniqueness, and all involution restrictions proved in the report. The source review is bounded. No exhaustive priority claim is made; Min's 2002 thesis was not inspected. General algebraicity for this type of restricted separable class predates this report.

## Contents

- `Report149.pdf` and `Report149.tex`: the self-contained report and editable LaTeX source
- `companion/`: newly written Python standard-library exact arithmetic, permutation checks, semantic evidence validation, and tests
- `SOURCE_PROVENANCE.json`: source URLs, reviewed theorem locations, source hashes, and the boundary between fresh package checks and earlier corroborating checks
- `build_pdf.py`: clean deterministic PDF builder with shell escape disabled and warning-free settled-log validation
- `make_zip.py`: fixed-allowlist archive builder that verifies the frozen checksum manifest before archiving
- `release_tools.py` and `test_release.py`: output-safety primitives and adversarial release tests
- `SHA256SUMS`: SHA-256 hashes for every other archive member

The archive excludes downloaded papers, previous reports, working notes, and build intermediates. Nothing has been submitted to OEIS, published, or changed in a repository as part of preparing this report.

## Requirements

The companion needs Python 3.10 or later and only the standard library. Output creation requires POSIX `O_NOFOLLOW` and `O_DIRECTORY`. The PDF builder additionally requires Linux `/proc/self/fd`, TeX Live with `pdftex` and `pdflatex`, Latin Modern, amsmath/amsthm/mathtools, geometry, booktabs/longtable/array, microtype, and hyperref. It uses the Debian-style system trees `/usr/share/texlive/texmf-dist` and `/usr/share/texmf`. No network access or installation is required on the tested environment.

PDF bytes are reproducible on the tested pdfTeX 1.40.26 / TeX Live 2025-dev Debian toolchain. A different TeX installation may render an equivalent report with different bytes. ZIP construction uses stored members, normalized metadata, and sorted names, avoiding compressor-version variation.

## Exact verification

Run from the extracted package root. Output parents must already exist. Each output target must be new; existing targets, parent traversal, and symlink destination components are refused. A failed build can leave a new diagnostic directory, which is never overwritten automatically.

```sh
mkdir validation
sha256sum -c SHA256SUMS
python3 companion/verify.py --output validation/evidence.json
python3 -O companion/verify.py --output validation/evidence-optimized.json
cmp companion/evidence.json validation/evidence.json
cmp validation/evidence.json validation/evidence-optimized.json
python3 -m unittest discover -s companion/tests -v
python3 -O -m unittest discover -s companion/tests -v
python3 -m unittest test_release -v
python3 -O -m unittest test_release -v
```

The companion README gives the exact finite bounds and additional evidence-check command. Its checks compare independently implemented recurrence and radical coefficients, inspect both smallest omitted permutations under both strict Baxter definitions, enumerate finite classes, and check formal inverse algebra. Tests reject mutations and remain active under `python3 -O`.

## Rebuild the PDF and source archive

```sh
python3 build_pdf.py --output-dir validation/pdf-a
python3 build_pdf.py --output-dir validation/pdf-b
cmp Report149.pdf validation/pdf-a/Report149.pdf
cmp validation/pdf-a/Report149.pdf validation/pdf-b/Report149.pdf
python3 make_zip.py --output validation/source-a.zip
python3 make_zip.py --output validation/source-b.zip
cmp validation/source-a.zip validation/source-b.zip
```

The PDF builder creates its own clean format and isolated TeX state, explicitly loads only its required font maps, and runs until auxiliary references stabilize. It rejects warnings, overfull or underfull boxes, and missing-character messages in the settled log. It uses descriptor-pinned output directories so a symlink component is not followed while creating outputs.

The ZIP builder validates the fixed sorted checksum manifest and every allowlisted input before creating a fresh output. Extra files in the extracted directory do not enter the archive. An altered payload is rejected rather than silently given a new checksum. `SHA256SUMS` provides consistency, not cryptographic authenticity against an attacker who can replace both the data and manifest.

## What the inverse bounds do and do not certify

Each parity threshold is bounded by ceilings of an explicit Lambert-W expansion plus and minus an asymptotic error. Taking the exact minimum of the two parity thresholds is essential. Eventually the combined bracket contains at most two adjacent full indices; exact coefficient evaluation resolves any ambiguity.

The error constants and onsets are existence results. The package does not supply effective finite-input constants certifying that a numerical asymptotic ceiling is correct for every input. Exact recurrence evaluation does give a finite threshold algorithm. Finite samples do not establish the infinite analytic remainder or replace the published structural inputs. The primary correction, the analytic theorem, and the computational checks are kept separate throughout.
