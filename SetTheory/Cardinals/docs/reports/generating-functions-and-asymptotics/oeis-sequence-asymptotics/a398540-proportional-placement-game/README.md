# Report 146

## All fixed orders for the proportional placement game

The article proves a logarithmic Poincare expansion for the placement probabilities
associated with OEIS A398540 at every fixed order M:

W_n / (A sqrt(n) r_*^n) = 1 + sum_{j=1}^M P_hat_j(log n)/n^j
                        + O_M((1+log n)^M/n^(M+1)),

where A = r_* sqrt(2 pi) and deg P_hat_j <= j-1.
The proof uses uniform signed convolution estimates, convergent subtracted endpoint
moments, and a finite scalar recursion. It also gives the explicit third-order term
with cancellation of its possible squared logarithm, the first logarithmic ratio
term, a logarithm-aware dyadic extrapolation, and all-fixed-order ceiling-safe
threshold inverses. A separate finite-coefficient rate-enclosure algorithm has a
proved quadratic-times-log interval-width bound.

All orders means every fixed finite truncation, with order-dependent error constants.
The report does not prove convergence of the infinite expansion, a complete
exponentially small transseries, effective correction remainder constants, a
computational-complexity bound, or new certified digits. No new rate-enclosure
iteration is executed. The numerical threshold brackets remain non-effective until
forward constants and errors can be enclosed.

## Contents

- `Report146.pdf` and `Report146.tex`: article and editable LaTeX source
- `companion/`: new standard-library exact-arithmetic checks, closed semantic
  fixtures, adversarial tests, and deterministic receipts
- `foundation/Report144.pdf`, `.tex`, `Report145.pdf`, and `.tex`: byte-unchanged
  foundation articles supplying the previously proved inputs
- `SOURCES.md`: source scope, dependency hashes, and reproduction boundaries
- `build_pdf.py`: clean deterministic PDF build
- `build_archive.py`: deterministic allowlisted ZIP build
- `toolchain.json`: recorded reproduction tool versions
- `SHA256SUMS`: hashes of every other archive member

No primary copyrighted manuscript PDF, earlier computational archive, private
working notes, or development intermediates are included.

## Verify the archive

From the extracted `Report146` directory:

```sh
sha256sum -c SHA256SUMS
```

## Run the exact companion

Python 3.9 or later and its standard library on a POSIX system with directory-descriptor
and no-follow file operations suffice. No network, floating-point placement simulation,
or external Python package is used. The secure local file guards deliberately reject
platforms without the required POSIX support.

```sh
python3 -I companion/checks.py
python3 -I -O companion/checks.py
python3 -I companion/test_checks.py
python3 -I -O companion/test_checks.py
```

See `companion/README.md` for exact tested identities, fixture validation, optional
receipt output, and the distinction between analytic proof inputs and finite
recomputed checks. The finite tests do not prove the all-orders theorem, uniform
remainders, infinite-series convergence, or computability/complexity claims, and
they do not certify any new numerical constant or threshold.

## Rebuild the PDF

The reference build uses the TeX Live 2025/dev Debian installation recorded in
`toolchain.json`, with pdfTeX, LaTeX, Latin Modern, AMS packages, geometry,
microtype, booktabs, and hyperref. The script uses the Debian TeX resource
directories in its source. It needs `pdftex` and `pdflatex` on PATH; it never
fetches packages from the network.

```sh
python3 -I build_pdf.py --output-dir rebuilt-one
python3 -I build_pdf.py --output-dir rebuilt-two
cmp rebuilt-one/Report146.pdf rebuilt-two/Report146.pdf
cmp Report146.pdf rebuilt-one/Report146.pdf
```

Both output directories must be new, with existing nonsymlink parents. Parent
traversal in output paths is refused. The script creates a clean local HOME and
TeX configuration, generates a local format, disables shell escape, fixes the
source timestamp and locale, and builds until cross-references stabilize. It
rejects warnings, missing characters, and overfull/underfull boxes in the final
settled typesetting log; initial reference-settling notices are expected. The
explicit font-map setup suppresses the unused default-map lookup. The script does
not overwrite the distributed article or rebuild the foundation documents. A materially different
TeX/font toolchain can change PDF bytes without changing the mathematical content.

For visual review with Poppler:

```sh
pdftoppm -png rebuilt-one/Report146.pdf rendered-page
```

The final PDF is visually checked page by page for clipped equations, overlapping
text, missing glyphs, page numbers, and readable section transitions.

## Rebuild the ZIP

From the extracted directory, use a new output path:

```sh
python3 -I build_archive.py --output rebuilt-Report146.zip
```

The output ZIP may be inside the extracted directory: it is not in the fixed
allowlist. The builder includes only the listed payload files and generates
`SHA256SUMS`. It fixes sorted path order, timestamps (2026-10-03 00:00:00), Unix
permissions, and ZIP_STORED compression. It refuses overwrite, symlink output
parents, and parent traversal. Extra unlisted files are ignored. Regeneration
from unchanged extracted payload reproduces the distributed ZIP byte-for-byte.
