# Common-Digit Fabius Zonoids

This archive accompanies the 36-page report
**“Common-Digit Fabius Zonoids: Exact volumes, hyperbolic-secant geometry,
Bernoulli Gaussianization, and parameter jets.”**

The construction couples the geometric-uniform/Fabius family

\[
X_q=(1-q)\sum_{n\ge 0}q^nU_n,\qquad 0<q<1,
\]

at several parameter values by using the same independent
`Uniform[0,1]` digits `U_n`.  The report develops the resulting joint support,
cumulants, covariance geometry, Gaussian limit, parameter jets, and links to
inverse Fabius, Legendre, Lambert-W, and Thue-Morse structures.

## Mathematical status

The report labels proved theorems, computational checks, conjectures, and
future directions separately.  The principal exact support-volume and
parameter-jet formulas are positive-parameter results.  Signed parameters
have changing minor orientations and are treated only in the conjectural
“oriented-matroid chambers” program.

The novelty claim is deliberately limited to **novelty relative to the audited
ProveIt documentation corpus**.  It is not an assertion that every theorem is
absent from all prior literature.  Classical ingredients such as zonotope
volume formulas, Schur/Littlewood identities, the hyperbolic-secant measure,
and Meixner-Pollaczek orthogonality are cited in the report.

## Archive contents

- `common_digit_fabius_zonoids.tex` — complete 2,092-line, 89,360-byte
  LaTeX source; SHA-256
  `ad6d0bfa137efe0c79cf0ee599845b8708d82ef31f6fc2c3016e80ff14a7675e`.
- `common_digit_fabius_zonoids.pdf` — synchronized 36-page, 1,171,153-byte
  report; SHA-256
  `4169b907f96b46cb75b1aab067e237a431798cfb612bbad11e2a74a38d494cd4`.
- `code/experiments.py` — fully commented symbolic/numerical experiment script.
- `generated/*.csv` — numerical and exact-symbolic verification tables.
- `generated/legendre_coefficients.tex` — exact symbolic coefficient table.
- `generated/*.pdf` and `generated/*.png` — vector and raster report figures.
- `generated/exact_summary.txt` — software versions, random seed, and check summary.
- `SOURCE_AUDIT.md` — repository-reading and novelty-boundary notes.
- `requirements.txt` — Python dependencies used for the supplied outputs.
- Package-local `SHA256SUMS*` ledgers are retired; Git history preserves the
  former package manifest and its arrival evidence, including its exact bytes,
  without making a checksum manifest a live dependency.

## Build the PDF

A TeX Live installation containing Libertinus, AMS packages,
`mathtools`, `cleveref`, `booktabs`, `longtable`, `microtype`, `listings`, and
`hyperref` is required.

From clean auxiliaries in the archive root, run exactly three serial passes:

```bash
pdflatex -interaction=nonstopmode -halt-on-error common_digit_fabius_zonoids.tex
pdflatex -interaction=nonstopmode -halt-on-error common_digit_fabius_zonoids.tex
pdflatex -interaction=nonstopmode -halt-on-error common_digit_fabius_zonoids.tex
```

The synchronized repository PDF was rebuilt by that exact procedure on
2026-09-04 with pdfTeX 1.40.22. Starting from absent auxiliaries, the three
successful halt-on-error passes produced 34 pages/1,152,987 bytes, 36
pages/1,171,153 bytes, and 36 pages/1,171,153 bytes. All pages are A4 at
rotation zero, rendered, and contain extractable text. All 27 font rows are
embedded and subset, five are Libertinus, and none is Type 3. The source
selects the retained PNG figure twins because the vector plot companions
contain Type-3 fonts. The final log has no error, unresolved reference or
citation, rerun request, or overfull box; its two underfull notices are a
status-table cell and the long repository URL. Title, author, subject, and
keywords metadata are present. Representative title, body, table, figure, and
final pages passed visual inspection; generated sidecars were removed.

## Reproduce the experiments and figures

The supplied data were generated with Python 3.13.5, NumPy 2.3.5,
SymPy 1.14.0, and Matplotlib 3.10.8.

```bash
python -m venv .venv
. .venv/bin/activate                 # Windows PowerShell: .venv\Scripts\Activate.ps1
python -m pip install -r requirements.txt
python code/experiments.py --output-root .
pdflatex -interaction=nonstopmode -halt-on-error common_digit_fabius_zonoids.tex
pdflatex -interaction=nonstopmode -halt-on-error common_digit_fabius_zonoids.tex
pdflatex -interaction=nonstopmode -halt-on-error common_digit_fabius_zonoids.tex
```

The script uses the fixed Monte Carlo seed `20260830`, records all numerical
parameters in `generated/exact_summary.txt`, and does not use Monte Carlo data
inside any proof.  SymPy is used for exact Euler-Hankel and Legendre checks;
NumPy is used for floating-point determinant and covariance checks.

## Validation and provenance

No package-local `SHA256SUMS*` ledger exists or should be recreated. The exact
three-pass build and PDF gates are recorded above, `SOURCE_AUDIT.md` records the
repository-reading boundary, and Git history preserves the retired package
evidence. The former manifest was validated at its archival checkpoint; that
historical verification result remains recoverable from Git history and is not
a current validation dependency.

The final PDF was rendered page-by-page at 170 dpi and visually checked for
clipped text, overlap, missing figures, black boxes, and broken glyphs.
