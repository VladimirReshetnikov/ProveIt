# Sharp moment bounds for the first zero and the zeros encoded in their errors

Open **paper.pdf**. The self-contained LaTeX source is **paper.tex**.

Theorem 1 gives alternating, multiplicity-sensitive errors for an estimator
of the leading spectral value. Corollary 2 and equation (4) recover the rest
of the spectrum from those errors. Theorem 3 identifies an exact optimum
for incomplete moment data and constructs the unique finite extremizer.
The zeta application includes both a rigorous four-moment enclosure and a
separate high-precision numerical experiment through the fourth ordinate.

## Reproduce

Run the following from the extracted directory, with Python assertions enabled.
All checks except the last use the Python standard library.

```sh
pdflatex -halt-on-error paper.tex
pdflatex -halt-on-error paper.tex
python3 verification/check_rational.py
python3 verification/check_endpoint.py
python3 verification/certify_moments.py
python3 verification/zeta_finite.py verification/certified_moments.json
python3 verification/zeta_example.py
```

The generator writes certified_moments.json beside itself. It reproduces the
certified data from the pinned ProveIt Li–Ritz packet. zeta_finite.py then
checks the order-three and order-four extremizers and the displayed bounds
using exact rational arithmetic. check_rational.py verifies the asymptotic
signs and tie factors in a finite example at the listed strides.
check_endpoint.py certifies an attained endpoint with a double largest value.

zeta_example.py uses mpmath 1.3.0. It samples the completed zeta function,
computes its center coefficients and reports nonrigorous numerical estimates.
Use --digits 185 --nodes 240 for the independent precision check. The two
runs printed the same displayed values. Reference zeros are computed only
after reconstruction. Expected outputs accompany the scripts.

sources/ gives the source comparison and the coverage of the repository
screen. Historical priority of the combined theorem is provisional.
SHA256SUMS records the delivered files; run sha256sum -c SHA256SUMS before
rebuilding the PDF to check them.
