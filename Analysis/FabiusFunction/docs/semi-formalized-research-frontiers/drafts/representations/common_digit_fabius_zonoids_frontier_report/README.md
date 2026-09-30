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

**Erratum (2026-09-29).** The report's conjecture `conj:jet-small-ball`
(subsection "Jet small balls and Lambert phases") is false as stated
whenever `q ≠ 1/e`: the small-ball logarithm contains the unbounded term
`((m+1)² log λ/λ) log log(1/x)`, `λ = −log q`, which its shape omits.
For `m = 0`, `q = 1/2` this term is already part of the machine-checked
Fabius small-argument expansion
(`Fabius.log_fabius_sub_explicitCorrectedWikipediaMain_isBigO`, whose main
term `fabiusWikipediaElementaryMain` contains `(log log 2/log 2) log L`).
An editorial note under the conjecture, marked `% ed.` in the source,
records the correct form; the conjecture itself is kept unchanged and
unrenumbered.  The general proof is the unreviewed draft
`../Polynomial_Geometric_Small_Deviations_Fabius_Jets/` (filed
2026-09-29).

## Archive contents

- `common_digit_fabius_zonoids.tex` — complete 2,134-line, 91,767-byte
  LaTeX source (2,092 lines before the editorial notes of 2026-09-29).
- `common_digit_fabius_zonoids.pdf` — synchronized 36-page, 1,296,128-byte
  report, rebuilt on 2026-09-29.
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

After the editorial note of 2026-09-29 under `conj:jet-small-ball`, the PDF
was rebuilt by the same three-pass procedure with MiKTeX pdfTeX 1.40.29:
36 pages, 1,295,227 bytes; the final log has no warning, error,
unresolved reference, rerun request, or overfull box, and the page
carrying the note was rendered and inspected.  After the second editorial
note of 2026-09-29 (below `conj:copula-endpoints`; see Editorial
amendments), the PDF was rebuilt again by the same procedure: 36 pages,
1,296,128 bytes; no error, unresolved reference, rerun request, duplicate
destination or overfull box, the same two underfull notices, no Type 3
font; the page carrying the note was rendered and inspected.  The SHA-256 values that
earlier versions of this README recorded described the 2026-09-04 build;
the repository no longer keeps checksum receipts.

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

## Editorial amendments (ProveIt, 2026-09-29)

- Under `conj:jet-small-ball`: the erratum note described in the Erratum
  paragraph above (after batch 50 of `docs/incoming/`).
- After the paragraph following `conj:copula-endpoints` (subsection
  "Inverse-Fabius copula endpoint laws"), in the editorial pass after batch
  54 of `docs/incoming/` (see `docs/incoming/README.md`): a note, marked
  `% ed.`, records that joint lower-corner small-deviation rates of the
  common-digit family, their first correction, the standardized copula
  exponent and conditional extremes given threshold events such as
  `{X_{1/2} <= x}` are proved in the unreviewed draft
  `../Endpoint_Geometry_Common_Digit_Fabius_Laws/` (its `thm:sharp`,
  `thm:copula`, `thm:diagonal` and `eq:conditional-threshold`), while
  `conj:copula-endpoints` and conditioning on an exact value `X_{1/2} = x`
  remain open.  The PDF was rebuilt as recorded under "Build the PDF".
