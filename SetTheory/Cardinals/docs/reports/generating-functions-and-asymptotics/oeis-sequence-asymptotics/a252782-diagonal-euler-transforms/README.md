# Report 147 Diagonal Euler transforms

This package accompanies the PDF on A252782 and A270917. It proves the corrected root limit 3^(1/3), residue amplitudes, all-depth exponential-polynomial sectors with a uniform remainder, the first unrestricted/distinct difference, all-orders smooth-model inverses and asymptotic integer threshold brackets, strict increase at every positive index, and a uniform critical crossover for a separately varying exponent.

The classical integer-break step is identified as classical. The source comparison corrects the conjectures in the inspected OEIS pages and makes no global priority claim. Public sources were inspected on 3 October 2026; crawl and site-footer dates are not asserted to be entry-specific revision dates.

## Read first

- `Report147.pdf`: complete mathematical report
- `Report147.tex`: editable, self-contained LaTeX source
- `companion/README.md`: exact computational checks and APIs
- `companion/certificate.json`: deterministic exact-arithmetic certificate

The integer threshold result is asymptotic. A particular finite-X certificate still needs verified model onsets, derivative and error inequalities, and a validated model-root computation. The explicit forward geometric-tail onset n >= 192 is not a universal inverse onset. The companion does not provide an interval solver. The all-index monotonicity proof removes a separate unknown finite-prefix maximum for these diagonal sequences.

The crossover theorem is uniform for 0 < z <= M, including z approaching zero, at each fixed M. The real-exponent extension is a formal signed model; the combinatorial interpretation uses integer exponents. The remaining open directions are stated as questions, not additional claims.

## Exact replay using only Python standard library

Use Python 3.10 or later. From the extracted package directory:

```sh
python3 -m unittest discover -s companion/tests -v
python3 -O -m unittest discover -s companion/tests -v
python3 companion/certificate.py > /tmp/report147-certificate-replayed.json
cmp companion/certificate.json /tmp/report147-certificate-replayed.json
```

Use a new temporary output name if that path already contains a file you wish to preserve. Shell redirection is shown explicitly. The program also accepts `--output` for a new path inside the companion directory, with existing paths, parent traversal and symlink components rejected.

The checks compare full coefficient rows from three independent extraction mechanisms, literal off-core profile sums, exact prefixes, exhaustive rational phase certificates, normalized coefficients, inverse algebraic ingredients, and crossover polynomial identities. They do not infer infinite asymptotic statements from a finite sample. Failure checks remain active under `-O`.

## Clean PDF build

Requirements: Python 3.10+, a Debian-style TeX Live installation with `pdftex`, `pdflatex`, the LaTeX base and recommended mathematics packages, `lmodern`, `microtype`, `geometry`, `booktabs`, and `hyperref`. The build script uses the installed trees `/usr/share/texlive/texmf-dist` and `/usr/share/texmf`, and sets a clean local TeX environment. No Python packages or network are needed.

Run from the extracted directory, choosing output paths that do not yet exist:

```sh
python3 build_pdf.py --output-dir /tmp/report147-build-a
python3 build_pdf.py --output-dir /tmp/report147-build-b
cmp /tmp/report147-build-a/Report147.pdf /tmp/report147-build-b/Report147.pdf
cmp Report147.pdf /tmp/report147-build-a/Report147.pdf
```

The last comparison is byte-exact on the TeX distribution used for delivery. Other TeX/font versions can produce different PDF bytes while rendering the same mathematics. The script creates a local format, disables shell escape, fixes the source epoch to 2026-10-03 00:00 UTC, suppresses volatile PDF metadata, stabilizes cross-references, and fails on warnings or overfull/underfull boxes in the final settled typesetting log. It explicitly clears the default font map before loading the four required maps. Initial-pass reference and table-width notices may appear while the cross-references settle. It refuses existing output directories and symlink components.

For visual review, with Poppler installed:

```sh
mkdir /tmp/report147-pages
pdftoppm -scale-to 1400 -png Report147.pdf /tmp/report147-pages/page
```

## Deterministic archive and integrity

The archive is a flat project tree, not a recursive dump of a working directory. `make_zip.py` contains the exact allowlist. It stores files without compression, in sorted order, with fixed timestamps and permissions, and adds `SHA256SUMS` covering every other member. No absolute file paths, bytecode, build logs, draft notes, or intermediate page images are included.

```sh
sha256sum -c SHA256SUMS
python3 make_zip.py --output /tmp/Report147-source-replay-a.zip
python3 make_zip.py --output /tmp/Report147-source-replay-b.zip
cmp /tmp/Report147-source-replay-a.zip /tmp/Report147-source-replay-b.zip
unzip -l /tmp/Report147-source-replay-a.zip
```

Use new output paths; archive creation refuses overwrites and symlink paths. Archive reproducibility follows from identical allowlisted input bytes. `SHA256SUMS` itself is generated by the packager and is deliberately not self-hashed.

## Files in the source archive

- `README.md`
- `Report147.pdf`
- `Report147.tex`
- `build_pdf.py`
- `make_zip.py`
- `companion/README.md`
- `companion/certificate.json`
- `companion/certificate.py`
- `companion/crossover.py`
- `companion/diagonal_euler.py`
- `companion/fixtures.py`
- `companion/tests/test_exact.py`
- `companion/tests/test_crossover.py`
- `SHA256SUMS`

The package makes no external publication, repository write, OEIS submission, or contact with sequence authors.
